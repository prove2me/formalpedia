-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_surjective_comap_of_isIntegral
-- name    : GlobalTheory.AffinePoints.surjective_comap_of_isIntegral
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:54:56.074402+00:00
-- url     : https://prove2.me/theorems/2dd52e9c-75af-47fe-97fa-2be684ff2705
-- title:
--   Affine Points: surjective comap of is Integral
-- statement:
--   The Affine Points construction uses the surjective comap of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsApplyEqZeroAndEqOne.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsApplyEqZeroAndEqOne.lean#L40-L45

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

theorem GlobalTheory.AffinePoints.surjective_comap_of_isIntegral {K A B : Type*} [Field K] [IsAlgClosed K] [CommRing A]
    [Algebra K A] [CommRing B] [Algebra K B] (φ : A →ₐ[K] B) (hφ : φ.toRingHom.IsIntegral)
    (hinj : Function.Injective φ) :
    Function.Surjective (comap φ : (B →ₐ[K] K) → (A →ₐ[K] K)) := by sorry
