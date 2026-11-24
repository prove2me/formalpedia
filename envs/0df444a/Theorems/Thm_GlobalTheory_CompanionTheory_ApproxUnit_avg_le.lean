-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ApproxUnit_avg_le
-- name    : GlobalTheory.CompanionTheory.ApproxUnit.avg_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:17:46.260191+00:00
-- url     : https://prove2.me/theorems/e12b0e37-09ca-449b-8b67-b044553bd9b6
-- title:
--   Approx Unit: avg le
-- statement:
--   The Approx Unit construction uses the avg le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CvAdjEqAvg.lean#L11-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CvAdjEqAvg.lean#L11-L46

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CvAdjEqAvg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ApproxUnit

theorem GlobalTheory.CompanionTheory.ApproxUnit.avg_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (b : α → ℝ) (u : α → ℂ) (c : ℂ)
    (ε : ℝ) (hb0 : ∀ w, 0 ≤ b w) (hb1 : ∫ w, b w ∂μ = 1) (hum : AEStronglyMeasurable u μ)
    (h : ∀ w, b w ≠ 0 → ‖u w - c‖ ≤ ε) :
    ‖∫ w, u w * (b w : ℂ) ∂μ - c‖ ≤ ε := by sorry
