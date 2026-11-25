-- Prove2me | Theorems.Thm_GlobalTheory_PoincareBounds_pdiag_term_le
-- name    : GlobalTheory.PoincareBounds.pdiag_term_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:50:58.873175+00:00
-- url     : https://prove2.me/theorems/c2bb16f1-3aac-4185-905a-0ba71bbba3ac
-- title:
--   Poincare Bounds: pdiag term le
-- statement:
--   The Poincare Bounds construction uses the pdiag term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PoincareMetricPuncturedPolydiscBounds.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PoincareMetricPuncturedPolydiscBounds.lean#L55-L59

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

theorem GlobalTheory.PoincareBounds.pdiag_term_le {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (ξ : Fin n → ℂ) (k : Fin n) :
    pdiag a z k * ‖ξ k‖ ^ 2 ≤ gnorm (poincareGram a z) ξ ^ 2 := by sorry
