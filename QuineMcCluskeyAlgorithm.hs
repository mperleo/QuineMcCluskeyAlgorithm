{-
	TRABAJO HASKELL - Algoritmo de Quine McCluskey

	Sergio Vicente San Gregorio - 71040469R
	Saul Refoyo Ferrero - 71045309B
	Miguel Perez Leon - 71046648Q

	11/05/2019
-}

import System.Environment
import Data.List

{----------------------------------------------------------------------------------------------------------------}
-- PROGRAMA PRINCIPAL
-- Recibe un argumento (archivo de texto) y simplifica la función contenida en dicho archivo
-- Guarda la solución en otro archivo.
{----------------------------------------------------------------------------------------------------------------}

main = do
  args@(l:_) <- getArgs -- guardo los argumentos en una lista
  texto <- readFile l -- leo el contenido del fichero
  let funcion = listaMinterms texto -- a partir de la lista con la funcion creo una lista de listas con los minterms indicados en el fichero
  print "Funcion"
  print funcion -- muestro los minterms en forma de listas de listas
  let implicantesfunc = implicantesFinal funcion -- calculo los implicantes más agrupados de la función
  print "Implicantes"
  print implicantesfunc -- muestro los implicantes de la funcion
  let funcionSimplificada = simplifica implicantesfunc -- calculo los implicantes que forman función simplificada
  print "Funcion simplificada"
  print funcionSimplificada -- muestro los implicantes que forman la función simplificada
  let funcionConVariables = funcionTexto funcionSimplificada -- transformo la lista de listas con los implicantes en una cadena con la función
  print funcionConVariables -- muestro la función simplificada
  writeFile "solución.txt" funcionConVariables -- guardo la función resultado en un fichero como se indica


{----------------------------------------------------------------------------------------------------------------}
-- LECTURA Y DE LOS DATOS DEL FICHERO A LOS QUE USA EL PROGRAMA
{----------------------------------------------------------------------------------------------------------------}

-- quita los caracteres de control de la string que pasamos y devuelve otra lista sin ellos.
nuevaCadCar "" = []
nuevaCadCar str@(x:xs) | x == '1' = 1:nuevaCadCar xs
                       | x == '0' = 0:nuevaCadCar xs
                       | otherwise = nuevaCadCar xs

-- calcula el número de variables que hay en el minterm
tamMinterm "" = 0
tamMinterm str@(x:xs) | x == '1' = 1+tamMinterm xs
                      | x == '0' = 1+tamMinterm xs
                      | otherwise = 0

-- parte una lista en sublistas de tamaño n
parteLista [] _ = []
parteLista l n = take n l:(parteLista (drop n l) n)

-- transforma la entrada de texto del fichero en una lista de listas con los minterms del enunciado propuesto
listaMinterms str = parteLista (nuevaCadCar str) n
  where n = tamMinterm str


{----------------------------------------------------------------------------------------------------------------}
-- PRIMER PASO, IDENTIFICACION DE LOS IMPLICANTES PRIMOS
{----------------------------------------------------------------------------------------------------------------}

-- Comprueba si se puede agrupar un minterm con los anteriores, si no se puede agupar se devuelve el minterm,
-- Si hay alguna agrupación se devuelve una lista vacía
implicantesConAnteriores x l1 = if length( grupos (x: l2)) == 0 then [x] else []
  where l2 = anteriores l1 x

-- Dada una lista (l:ls) y un elemento (x) de esta devuelve una lista con todos los elementos anteriores
-- A la primera aparición de x en la lista
anteriores [] x = []
anteriores (l:ls) x = if x == l then [] else l:(anteriores ls x)

-- Genera los implicantes de la lista que pasamos.
-- Se comparan todos los minterms con los siguientes
-- Si no se puede agrupar con los siguientes, comprobamos si se puede agrupar con los anteriores
-- Si no se puede, esque esta reducido al máximo y se añade a la solucion.
implicantes [] [] = []
implicantes [l] lo = implicantesConAnteriores l lo
implicantes l1@(l:ls) lo= if length l2 > 0 then l2++(implicantes (ls) lo) else if length(implicantesConAnteriores l lo) == 1 then [l]++(implicantes (ls) lo) else implicantes (ls) lo
  where l2 = grupos l1

-- Se le pasa una lista con los minterms
-- en l2 se guardan las agrupaciones de todo
-- Si l2 es distinto de l1 se repite recursivamente hasta que ya no se pueden agrupar mas
-- Calcula los implicantes hasta que son irreducibles.
implicantesFinal l1@(l:ls) = if l1 /= l2 then implicantesFinal (quitaDobles l2) else l2
  where l2 = implicantes l1 l1

-- Función que deja solo una aparición de un elemento que se repite varias veces en la lista
quitaDobles [] = []
quitaDobles [x] = [x]
quitaDobles l@(l1:ls) = if elem l1 ls then l1:(quitaDobles l2) else l1:(quitaDobles ls)
  where l2 = filter (/= l1) ls

-- Devuelve una lista con las combinaciones del primer elemento de la lista con todos los siguientes,
-- Si tienen agrupacion.
grupos :: [[Int]]->[[Int]]
grupos [] = []
grupos [lx]= []
grupos [lx,ly] = if (comprobar lx ly) == 1 then [nuevoTermino lx ly] else []
grupos l1@(lx:ly:ls) = if comprobar lx ly == 1 then nuevo:(grupos (lx:ls)) else grupos (lx:ls)
  where nuevo = nuevoTermino lx ly

-- Devuelve el numero de cambios que hay entre dos listas pasadas
comprobar l [] = 0
comprobar [] l = 0
comprobar [x] [y] = if x == y then 0 else 1
comprobar (x:xs) (y:ys) = if x == y then comprobar xs ys else 1+(comprobar xs ys)

-- Devuelve las listas uniendo los dos minterms, si en la misma posicion son distintos,
-- En la lista que devuelve la solucion sale -1 y si son iguales sale el propio termino.
nuevoTermino [] [] = []
nuevoTermino [xs] [] = [xs]
nuevoTermino [] [xs] = [xs]
nuevoTermino (x:xs) (y:ys) = if x == y then x:(nuevoTermino xs ys) else (-1):(nuevoTermino xs ys)


{----------------------------------------------------------------------------------------------------------------}
-- SEGUNDO PASO, SIMPLIFICACION DE LA FUNCION
{----------------------------------------------------------------------------------------------------------------}

-- Funcion que dada una lista binaria la transforma en una lista de los minterms que la componen
listaminterm [] = []
listaminterm l = listaaminterm (reverse l) 0

-- Funcion auxiliar de listaminterm
-- B representa la potencia de 2 de la posicion del bit
-- El (-1) representa el 0 o 1 por
listaaminterm [] _ = [0]
listaaminterm (x:xs) b = if x/=(-1) then map ((x*2^b)+) (listaaminterm xs (b+1)) else map ((0*2^b)+) (listaaminterm xs (b+1) ) ++ map ((1*2^b)+) (listaaminterm xs (b+1) )

-- Funcion que devuelve la lista de booleanos que indica los terminos que van a ser usados y cuales no
-- La funcion es recursiva se repite tantas veces como sea la longitud de la lista, indicado el valor por n
-- En cada iteracion si el termino no va a ser usado este se ignora en la recursividad, si se usa se considera para
-- Las siguientes comparaciones
listaboleana [] _ = []
listaboleana _ 0 = []
listaboleana (x:xs) n = if all (==True) l then False:listaboleana xs (n-1) else True:listaboleana (xs++[x]) (n-1)
  where l = buscarminterms x xs

-- Funcion auxiliar de listaboleana, esta funcion dado una lista de minterms y una lista de listas de minterm
-- Da como resultado una lista boleana que indica si cada termino se repite en la lista de listas
-- Si en la lista que devuelve todos los valores son verdaderos esto indica que el termino que representa se puede
-- Eliminar de interpretar este resultado se encarga la funcion de listabooleana
buscarminterms x xs = [any (==True) (map (elem y) xs)| y<-x]

-- Dada una tupla que contiene el termino y el valor boleano que indica si este se usa o no, esta funcion
-- Se encarga de eliminar los terminos que no se van a usar
descartaFalsos [] = []
descartaFalsos ((m,b):xs) = if b==True then m:descartaFalsos xs else descartaFalsos xs

-- Dada la funion boleana en forma de una lista de listas esta funcion se encarga de eliminar los terminos redundantes
simplifica [] = []
simplifica l = descartaFalsos (zip l (l2))
  where l2 = listaboleana (map listaminterm l) (length l)


{----------------------------------------------------------------------------------------------------------------}
-- TEXTO PARA EL FICHERO DE SALIDA
{----------------------------------------------------------------------------------------------------------------}

-- Array con el abecedario para pasar de la solucíon como cadenas en binario a la función con las letras
letras :: [Char]
letras = " ABCDEFGHIJKLMNOPQRSTUVWXYZ"

-- Convierte una lista de números binarios en un termino con variables
convertir [] _ = ""
convertir l@(x:xs) n  | x == 1 = (letras!!(n)) : (convertir xs (n+1))
                      | x == 0 = (letras!!(n)) : '\'' : (convertir xs (n+1))
                      | otherwise = convertir xs (n+1)

-- Convierte una lista de listas binarias en los terminos que le corresponde
funcionTexto [] = ""
funcionTexto [x] =  convertir x 1
funcionTexto l@(x:xs) = (convertir x 1) ++ " + " ++  (funcionTexto xs )
