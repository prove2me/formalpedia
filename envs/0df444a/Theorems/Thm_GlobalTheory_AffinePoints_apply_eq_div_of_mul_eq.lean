-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_apply_eq_div_of_mul_eq
-- name    : GlobalTheory.AffinePoints.apply_eq_div_of_mul_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:59.832747+00:00
-- url     : https://prove2.me/theorems/ce202a50-955c-49a3-8c94-3eaad22002bd
-- title:
--   Affine Points: apply eq div of mul eq
-- statement:
--   The Affine Points construction uses the apply eq div of mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ContinuousAevalMvPolynomial.lean#L182-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ContinuousAevalMvPolynomial.lean#L182-L185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set
variable {R A B K : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B] [Field K] [Algebra R K]

theorem GlobalTheory.AffinePoints.apply_eq_div_of_mul_eq (q : B →ₐ[R] K) {b : B} {a s : A} (hs : IsUnit (algebraMap A B s))
    (h : b * algebraMap A B s = algebraMap A B a) :
    q b = q (algebraMap A B a) / q (algebraMap A B s) := by sorry
