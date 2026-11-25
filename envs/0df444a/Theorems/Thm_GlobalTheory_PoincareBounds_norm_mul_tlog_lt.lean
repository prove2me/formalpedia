-- Prove2me | Theorems.Thm_GlobalTheory_PoincareBounds_norm_mul_tlog_lt
-- name    : GlobalTheory.PoincareBounds.norm_mul_tlog_lt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:50:17.082871+00:00
-- url     : https://prove2.me/theorems/2d6f440b-bd21-463a-8779-9ef9450c22e2
-- title:
--   Poincare Bounds: norm mul tlog lt
-- statement:
--   The Poincare Bounds construction uses the norm mul tlog lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PoincareMetricPuncturedPolydiscBounds.lean#L29-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PoincareMetricPuncturedPolydiscBounds.lean#L29-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PoincareMetricPuncturedPolydiscBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.PoincareBounds

theorem GlobalTheory.PoincareBounds.norm_mul_tlog_lt {w : ℂ} (h0 : w ≠ 0) (h1 : ‖w‖ < 1) :
    0 < ‖w‖ * tlog w ∧ ‖w‖ * tlog w < 1 := by sorry
