-- Prove2me | Theorems.Thm_GlobalTheory_AugCot_map_surjective
-- name    : GlobalTheory.AugCot.map_surjective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:45:29.090802+00:00
-- url     : https://prove2.me/theorems/2d046453-7274-45f5-96a5-8ad6303d8897
-- title:
--   Aug Cot: map surjective
-- statement:
--   The Aug Cot construction uses the map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L331-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L331-L336

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

theorem GlobalTheory.AugCot.map_surjective (φ : A →ₐ[R] B) (h : εB.comp φ = εA) (hφ : Function.Surjective φ) :
    Function.Surjective (map φ h) := by sorry
