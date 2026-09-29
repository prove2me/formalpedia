-- Prove2me | Theorems.Thm_Matrix_charpoly_of_uString
-- name    : Matrix.charpoly_of_uString
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/0866c4d7-6cf6-5a56-91b4-8df66e2a9e86
-- title:
--   Characteristic polynomial of a U-string matrix
-- statement:
--   Let $F$ be a field, let $e$ be a natural number and let $a, b \in F$. Consider the $(e+1)\times(e+1)$ matrix $M$ over $F$, with rows and columns indexed by $\mathrm{Fin}(e+1)$, given by the explicit entry function: in column $j$ with $j = 0$, the entry in row $i$ is $a$ if $i = 0$, is $-b$ if $i = 1$, and is $0$ otherwise; in a column $j \neq 0$, the entry in row $i$ is $1$ if $i + 1 = j$ (as natural numbers) and $0$ otherwise. Thus column $0$ is $(a, -b, 0, \dots, 0)^{\mathsf T}$ and, for $j \geq 1$, column $j$ is the standard basis vector supported in row $j-1$. The assertion is that the characteristic polynomial of $M$, in the sense of `Matrix.charpoly`, equals $X - C\,a$ when $e = 0$, and equals $X^{e-1}\,(X^2 - C\,a\,X + C\,b)$ when $e \neq 0$, where $e - 1$ is truncated subtraction of natural numbers and $C$ denotes the constant-coefficient inclusion $F \to F[X]$.
--
--   The matrix is the matrix, in a basis $v_0, \dots, v_e$, of the operator sending $v_0 \mapsto a v_0 - b v_1$ and $v_j \mapsto v_{j-1}$ for $j \geq 1$; it is the shape taken by a Hecke operator on the string of oldform translates at a fixed prime, so the statement records that the relevant Hecke polynomial is $X^2 - aX + b$ times a power of $X$. It is used in the computation of the dimension of a simultaneous eigenspace/generalised eigenspace intersection inside a space of parabolic homomorphisms, where the factorisation determines root multiplicities.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_charpoly_of_uString.lean

import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Matrix.charpoly_of_uString (F : Type) [Field F] (e : ℕ) (a b : F) :
    (Matrix.of fun i j : Fin (e + 1) =>
        if (j : ℕ) = 0 then (if (i : ℕ) = 0 then a else if (i : ℕ) = 1 then -b else 0)
        else (if (i : ℕ) + 1 = (j : ℕ) then (1 : F) else 0)).charpoly =
      if e = 0 then X - C a else X ^ (e - 1) * (X ^ 2 - C a * X + C b) := by sorry
