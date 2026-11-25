-- Prove2me | Theorems.Thm_GlobalTheory_FlowProgramme_sum_shift
-- name    : GlobalTheory.FlowProgramme.sum_shift
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:15:19.341848+00:00
-- url     : https://prove2.me/theorems/fe4116eb-b149-4e5e-96b4-b29575a90254
-- title:
--   Flow Programme: sum shift
-- statement:
--   The Flow Programme construction uses the sum shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CyclicSolvable.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CyclicSolvable.lean#L7-L11

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

theorem GlobalTheory.FlowProgramme.sum_shift (d : ℕ) [NeZero d] (x : ZMod d → ℕ → ℝ) (s : Finset ℕ) :
    ∑ a : ZMod d, ∑ i ∈ s, x (a - i) i = ∑ a, ∑ i ∈ s, x a i := by sorry
