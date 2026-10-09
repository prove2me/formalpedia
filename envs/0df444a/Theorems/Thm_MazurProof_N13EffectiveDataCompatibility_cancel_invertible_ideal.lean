-- Prove2me | Theorems.Thm_MazurProof_N13EffectiveDataCompatibility_cancel_invertible_ideal
-- name    : MazurProof.N13EffectiveDataCompatibility.cancel_invertible_ideal
-- status  : Open
-- author  : @xuanji
-- created : 2026-10-09T03:25:17.810271+00:00
-- url     : https://prove2.me/theorems/d5743255-9306-41ba-be8f-bbb938bbe923
-- title:
--   Mazur 13 port: cancel_invertible_ideal
-- statement:
--   Supporting lemma `cancel_invertible_ideal` (namespace `MazurProof.N13EffectiveDataCompatibility`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13EffectiveDataCompatibility.lean#L45

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped nonZeroDivisors

theorem MazurProof.N13EffectiveDataCompatibility.cancel_invertible_ideal {T K : Type*} [CommRing T] [IsDomain T] [Field K] [Algebra T K] [IsFractionRing T K] (I J U : Ideal T) (hU : IsUnit (U : FractionalIdeal T⁰ K)) (h : I * U = J * U) : I = J := by sorry
