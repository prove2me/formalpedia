-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LowSpanCombinations_cpt_zero
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations.cpt_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:08:54.015538+00:00
-- url     : https://prove2.me/theorems/3fc68928-b485-51b2-9873-f344a7d61bb1
-- title:
--   Low Span Combinations: cpt zero
-- statement:
--   The Low Span Combinations construction uses the cpt zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/LowSpanCombinations.lean#L101-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/LowSpanCombinations.lean#L101-L110

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations.cpt_zero (X : Data E r) (x0 : Frame X.Ψ r) : cpt X x0 0 = x0 := by sorry
