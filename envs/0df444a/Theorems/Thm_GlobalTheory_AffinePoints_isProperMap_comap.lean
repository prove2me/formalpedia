-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_isProperMap_comap
-- name    : GlobalTheory.AffinePoints.isProperMap_comap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:19.095794+00:00
-- url     : https://prove2.me/theorems/dc12a0d2-2f37-4de5-9b19-bf964b7ca083
-- title:
--   Affine Points: is Proper Map comap
-- statement:
--   The Affine Points construction uses the is Proper Map comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsApplyEqZeroAndEqOne.lean#L69-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsApplyEqZeroAndEqOne.lean#L69-L102

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

theorem GlobalTheory.AffinePoints.isProperMap_comap (φ : A →ₐ[ℂ] B) (hφ : φ.toRingHom.IsIntegral) :
    IsProperMap (comap φ : (B →ₐ[ℂ] ℂ) → (A →ₐ[ℂ] ℂ)) := by sorry
