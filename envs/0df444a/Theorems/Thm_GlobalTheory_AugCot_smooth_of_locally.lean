-- Prove2me | Theorems.Thm_GlobalTheory_AugCot_smooth_of_locally
-- name    : GlobalTheory.AugCot.smooth_of_locally
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:46:12.743513+00:00
-- url     : https://prove2.me/theorems/7216a98c-7d44-432c-8c0c-bdec4fbee3c9
-- title:
--   Aug Cot: smooth of locally
-- statement:
--   The Aug Cot construction uses the smooth of locally property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L718-L723
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L718-L723

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
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R) {n : ℕ}

theorem GlobalTheory.AugCot.smooth_of_locally
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A)) :
    Algebra.Smooth R A := by sorry
