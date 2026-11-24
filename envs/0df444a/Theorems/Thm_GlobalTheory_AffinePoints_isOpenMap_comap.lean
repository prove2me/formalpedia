-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_isOpenMap_comap
-- name    : GlobalTheory.AffinePoints.isOpenMap_comap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:55:11.881098+00:00
-- url     : https://prove2.me/theorems/f9f18356-bdfc-4d40-8d95-ad2f178b690f
-- title:
--   Affine Points: is Open Map comap
-- statement:
--   The Affine Points construction uses the is Open Map comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsApplyEqZeroAndEqOne.lean#L133-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsApplyEqZeroAndEqOne.lean#L133-L185

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

theorem GlobalTheory.AffinePoints.isOpenMap_comap [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] (φ : A →ₐ[ℂ] B)
    (hφ : φ.Finite) (hinj : Function.Injective φ) :
    IsOpenMap (comap φ : (B →ₐ[ℂ] ℂ) → (A →ₐ[ℂ] ℂ)) := by sorry
