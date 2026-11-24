-- Prove2me | Theorems.Thm_GlobalTheory_AugCot_finrank_kaehler_of_isStandardSmoothOfRelativeDimension
-- name    : GlobalTheory.AugCot.finrank_kaehler_of_isStandardSmoothOfRelativeDimension
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:44:57.381155+00:00
-- url     : https://prove2.me/theorems/fe247c85-8c0f-4d73-a693-d5ec6d19cbcf
-- title:
--   Aug Cot: finrank kaehler of is Standard Smooth Of Relative Dimension
-- statement:
--   The Aug Cot construction uses the finrank kaehler of is Standard Smooth Of Relative Dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L690-L693
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L690-L693

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
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R)

theorem GlobalTheory.AugCot.finrank_kaehler_of_isStandardSmoothOfRelativeDimension [Nontrivial A] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R A] : Module.finrank A Ω[A⁄R] = n := by sorry
