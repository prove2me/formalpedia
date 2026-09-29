-- Prove2me | Theorems.Thm_LinearMap_charpoly_of_finrank_eq_two
-- name    : LinearMap.charpoly_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/6eb39757-9e30-581c-8cd4-f83b507a59f8
-- title:
--   Characteristic polynomial of a rank-two endomorphism
-- statement:
--   Let $R$ be a nontrivial commutative ring and $M$ an $R$-module that is free and finite over $R$, and suppose its rank satisfies $\mathrm{finrank}_R M = 2$. Then for every $R$-linear endomorphism $f \colon M \to M$, the characteristic polynomial of $f$ (the `LinearMap.charpoly` of Mathlib, defined via the matrix of $f$ in a chosen basis) is given by $$f.\mathrm{charpoly} = X^2 - C(\mathrm{tr}_R(f))\,X + C(\det f),$$ an identity in the polynomial ring $R[X]$, where $\mathrm{tr}_R(f)$ denotes `LinearMap.trace R M f`, $\det f$ denotes `LinearMap.det f`, and $C$ is the inclusion of $R$ as constant polynomials. The hypothesis of nontriviality of $R$ enters through the availability of a basis indexed by `Fin 2` for a module of finrank $2$.
--
--   This is the standard rank-two case of the formula expressing the characteristic polynomial through the coefficients trace and determinant. It serves as the dictionary between the two usual formulations of the data attached to a two-dimensional Galois representation — 'characteristic polynomial of Frobenius' versus 'trace and determinant of Frobenius' — and is used in that role in the statements about Galois representations attached to newforms and to Tate modules of elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_charpoly_of_finrank_eq_two.lean

import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Determinant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem LinearMap.charpoly_of_finrank_eq_two {R : Type*} {M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (h : Module.finrank R M = 2) (f : M →ₗ[R] M) : f.charpoly = X ^ 2 - C (LinearMap.trace R M f) * X + C (LinearMap.det f) := by sorry
