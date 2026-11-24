-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HodgePeriodGram_tlog_pos
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog_pos
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:45:16.599424+00:00
-- url     : https://prove2.me/theorems/feb6ddc3-9c31-477a-a6e0-37b0f4305385
-- title:
--   Hodge Period Gram: tlog pos
-- statement:
--   The Hodge Period Gram construction uses the tlog pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/HodgePeriodGram.lean#L75-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/HodgePeriodGram.lean#L75-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
open GlobalTheory.HermFrame
variable {n a g : ℕ}
open Matrix Complex Filter Topology
open scoped ComplexOrder
variable {n a g : ℕ}

theorem GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog_pos {w : ℂ} (h0 : w ≠ 0) (h1 : ‖w‖ < 1) : 0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog w := by sorry
