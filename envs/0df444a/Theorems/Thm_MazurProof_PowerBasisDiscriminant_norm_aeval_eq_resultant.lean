-- Prove2me | Theorems.Thm_MazurProof_PowerBasisDiscriminant_norm_aeval_eq_resultant
-- name    : MazurProof.PowerBasisDiscriminant.norm_aeval_eq_resultant
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:24:57.981329+00:00
-- url     : https://prove2.me/theorems/443f14d8-4db0-4738-928d-071707daa9fc
-- title:
--   Mazur 13 port: norm_aeval_eq_resultant
-- statement:
--   The norm of a polynomial in a power-basis generator is the resultant with the generator's minimal polynomial.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/PowerBasisDiscriminant.lean#L32

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
open scoped Polynomial BigOperators

theorem MazurProof.PowerBasisDiscriminant.norm_aeval_eq_resultant {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] (B : PowerBasis K L) (q : K[X]) : Algebra.norm K (Polynomial.aeval B.gen q) = (minpoly K B.gen).resultant q := by sorry
