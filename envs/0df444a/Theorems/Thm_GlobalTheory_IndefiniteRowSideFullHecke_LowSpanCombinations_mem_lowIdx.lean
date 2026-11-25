-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LowSpanCombinations_mem_lowIdx
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations.mem_lowIdx
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:09:19.854031+00:00
-- url     : https://prove2.me/theorems/f5cc97fa-62fc-4ff4-a1b0-31dda4a1a0f2
-- title:
--   Low Span Combinations: mem low Idx
-- statement:
--   The Low Span Combinations construction uses the mem low Idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/LowSpanCombinations.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/LowSpanCombinations.lean#L69-L73

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_LowSpanCombinations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations.mem_lowIdx {D T : ℕ} {al : Fin D → ℕ} : al ∈ lowIdx D T ↔ ∑ i, al i + D < T := by sorry
