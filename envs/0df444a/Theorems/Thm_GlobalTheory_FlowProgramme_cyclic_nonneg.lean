-- Prove2me | Theorems.Thm_GlobalTheory_FlowProgramme_cyclic_nonneg
-- name    : GlobalTheory.FlowProgramme.cyclic_nonneg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:30.676203+00:00
-- url     : https://prove2.me/theorems/47b31b65-bb0e-42d1-985d-7c96a65241b9
-- title:
--   Flow Programme: cyclic nonneg
-- statement:
--   The Flow Programme construction uses the cyclic nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CyclicSolvable.lean#L57-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CyclicSolvable.lean#L57-L71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_WtSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CyclicSolvable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory GlobalTheory.FlowProgramme

theorem GlobalTheory.FlowProgramme.cyclic_nonneg (l : ℝ) (d : ℕ) [NeZero d] (X y : ZMod d → ℝ) (hl : 2 ≤ l)
    (hX : ∀ a b, X a ≤ l * X b) (hy : ∀ a, l * y a + y (a - 1) = X a) (a : ZMod d) :
    0 ≤ y a := by sorry
