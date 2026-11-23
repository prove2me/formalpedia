-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_exists_comap_eq_of_isIntegral
-- name    : GlobalTheory.AffinePoints.exists_comap_eq_of_isIntegral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:21.9481+00:00
-- url     : https://prove2.me/theorems/bafbea1d-2ffb-46b0-8167-dfd955c47d4c
-- title:
--   Affine Points: exists comap eq of is Integral
-- statement:
--   The Affine Points construction uses the exists comap eq of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsApplyEqZeroAndEqOne.lean#L11-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsApplyEqZeroAndEqOne.lean#L11-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowCardLeNormProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set Polynomial
variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

theorem GlobalTheory.AffinePoints.exists_comap_eq_of_isIntegral {K A B : Type*} [Field K] [IsAlgClosed K] [CommRing A]
    [Algebra K A] [CommRing B] [Algebra K B] (φ : A →ₐ[K] B) (hφ : φ.toRingHom.IsIntegral)
    (p : A →ₐ[K] K) (hp : ∀ a, φ a = 0 → p a = 0) : ∃ q : B →ₐ[K] K, comap φ q = p := by sorry
