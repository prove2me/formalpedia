-- Prove2me | Theorems.Thm_MazurProof_N13FormalCurveOverlap_affineCurve_relation
-- name    : MazurProof.N13FormalCurveOverlap.affineCurve_relation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T04:27:15.219984+00:00
-- url     : https://prove2.me/theorems/e918970e-c591-49ef-a5c2-a1e8cfb4d30f
-- title:
--   Mazur 13 port: affineCurve_relation
-- statement:
--   The proposed image of `y` satisfies the actual affine equation after the substitution `x=t⁻¹`.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13FormalCurveOverlap.lean#L360

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13FormalCurveOverlap
open Polynomial
open HahnSeries
open scoped LaurentSeries
attribute [local instance] MazurProof.N13FormalCurveOverlap.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13FormalCurveOverlap.affineCurve_relation : (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).eval₂ affineCoeffMap yImage = 0 := by sorry
