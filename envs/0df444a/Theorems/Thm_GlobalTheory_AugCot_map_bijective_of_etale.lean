-- Prove2me | Theorems.Thm_GlobalTheory_AugCot_map_bijective_of_etale
-- name    : GlobalTheory.AugCot.map_bijective_of_etale
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:46:03.361552+00:00
-- url     : https://prove2.me/theorems/ecc37b74-ea25-4547-abde-0f8b62fe32d4
-- title:
--   Aug Cot: map bijective of etale
-- statement:
--   The Aug Cot construction uses the map bijective of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L457-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L457-L461

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.AugCot
variable {R A B C : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [CommRing C] [Algebra R C] {εA : A →ₐ[R] R} {εB : B →ₐ[R] R} {εC : C →ₐ[R] R}

theorem GlobalTheory.AugCot.map_bijective_of_etale (φ : A →ₐ[R] B) (h : εB.comp φ = εA)
    (hφ : (φ : A →+* B).Etale) : Function.Bijective (map φ h) := by sorry
