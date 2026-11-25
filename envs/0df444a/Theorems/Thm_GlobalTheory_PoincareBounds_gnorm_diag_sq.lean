-- Prove2me | Theorems.Thm_GlobalTheory_PoincareBounds_gnorm_diag_sq
-- name    : GlobalTheory.PoincareBounds.gnorm_diag_sq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:50:14.7895+00:00
-- url     : https://prove2.me/theorems/4e5f957d-8be8-4001-ae7c-f66e54c45e1c
-- title:
--   Poincare Bounds: gnorm diag sq
-- statement:
--   The Poincare Bounds construction uses the gnorm diag sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PoincareMetricPuncturedPolydiscBounds.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PoincareMetricPuncturedPolydiscBounds.lean#L19-L27

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

theorem GlobalTheory.PoincareBounds.gnorm_diag_sq {n : ℕ} (d : Fin n → ℝ) (hd : ∀ k, 0 ≤ d k) (ξ : Fin n → ℂ) :
    gnorm (diagonal fun k => ((d k : ℝ) : ℂ)) ξ ^ 2 = ∑ k, d k * ‖ξ k‖ ^ 2 := by sorry
