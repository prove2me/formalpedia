-- Prove2me | Theorems.Thm_GlobalTheory_norm_pderivIter_le_of_nonneg
-- name    : GlobalTheory.norm_pderivIter_le_of_nonneg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:13:21.646788+00:00
-- url     : https://prove2.me/theorems/4eef25b8-96cc-41e3-9abc-e8b5d7df3a17
-- title:
--   Global Theory: norm pderiv Iter le of nonneg
-- statement:
--   The Global Theory construction uses the norm pderiv Iter le of nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/PderivIterEqPderivListOfDifferentiableOn.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/PderivIterEqPderivListOfDifferentiableOn.lean#L12-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormPderivIterLeOfAnalyticAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_PderivIterEqPderivListOfDifferentiableOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem GlobalTheory.norm_pderivIter_le_of_nonneg {F : (ι → ℂ) → V} {U : Set (ι → ℂ)} {a : ι → ℂ} {r : ι → ℝ}
    {M : ℝ} (α : ι →₀ ℕ) (hr : ∀ k, 0 ≤ r k) (hα : ∀ k, α k ≠ 0 → 0 < r k) (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hsub : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ ≤ r k) → z ∈ U)
    (hM : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ = r k) → ‖F z‖ ≤ M) :
    ‖pderivIter α F a‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, r k ^ α k := by sorry
