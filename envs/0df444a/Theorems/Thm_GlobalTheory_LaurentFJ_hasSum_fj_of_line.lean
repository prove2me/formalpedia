-- Prove2me | Theorems.Thm_GlobalTheory_LaurentFJ_hasSum_fj_of_line
-- name    : GlobalTheory.LaurentFJ.hasSum_fj_of_line
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:04:53.494501+00:00
-- url     : https://prove2.me/theorems/2ebc11e2-a45a-4ed6-8177-385ec28e94b8
-- title:
--   Laurent FJ: has Sum fj of line
-- statement:
--   The Laurent FJ construction uses the has Sum fj of line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CoeffEqZeroOfHasSumZero.lean#L113-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CoeffEqZeroOfHasSumZero.lean#L113-L162

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bExpHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CoeffEqZeroOfHasSumZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentFJ
open Complex ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}

theorem GlobalTheory.LaurentFJ.hasSum_fj_of_line (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (sb : X.Ψ → ℝ)
    (hint : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∃ k : ℤ, 2 * ∑ τ, ν τ * sb τ = k)
    (κ u₁ : ℂ) (a : ℤ → ℂ) (y : ℝ)
    (hdom : ∀ w : ℂ, w.im = y → X.flow ξ (fun τ => w * sb τ) x ∈ X.dom)
    (ha : ∀ w : ℂ, w.im = y → HasSum (fun n : ℤ => a n * (u₁ * cexp (2 * Real.pi * I * w)) ^ n)
      (κ * P (X.flow ξ (fun τ => w * sb τ) x))) (j : ℤ) :
    HasSum (fun ν : {ν : X.Ψ → ℝ // 2 * ∑ τ, ν τ * sb τ = j} => κ * X.fj la ξ ν P x)
      (a j * u₁ ^ j) := by sorry
