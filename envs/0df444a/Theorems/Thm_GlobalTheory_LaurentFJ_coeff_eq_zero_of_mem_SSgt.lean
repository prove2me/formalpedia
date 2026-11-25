-- Prove2me | Theorems.Thm_GlobalTheory_LaurentFJ_coeff_eq_zero_of_mem_SSgt
-- name    : GlobalTheory.LaurentFJ.coeff_eq_zero_of_mem_SSgt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:24:13.75179+00:00
-- url     : https://prove2.me/theorems/880bd71f-61ab-5bc6-8d68-81d2fb44e188
-- title:
--   Laurent FJ: coeff eq zero of mem SSgt
-- statement:
--   The Laurent FJ construction uses the coeff eq zero of mem SSgt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CoeffEqZeroOfHasSumZero.lean#L223-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CoeffEqZeroOfHasSumZero.lean#L223-L233

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

theorem GlobalTheory.LaurentFJ.coeff_eq_zero_of_mem_SSgt (X : Data E r) {la : Wt X.Ψ r} {c : ℝ} {P : Frame X.Ψ r → ℂ}
    (hP : P ∈ X.SSgt la c) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (sb : X.Ψ → ℝ) (hsb : ∀ τ, 0 < sb τ) (ν₀ : X.Ψ → ℝ) (hν₀ : ∑ τ, ν₀ τ ≤ c) (j : ℤ)
    (hj : 2 * ∑ τ, ν₀ τ * sb τ = j)
    (huniq : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → 2 * ∑ τ, ν τ * sb τ = j → ν = ν₀)
    (hint : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∃ k : ℤ, 2 * ∑ τ, ν τ * sb τ = k)
    (a : ℤ → ℂ) (T : ℝ)
    (ha : ∀ w : ℂ, T < w.im → HasSum (fun n : ℤ => a n * cexp (2 * Real.pi * I * w) ^ n)
      (P (X.flow ξ (fun τ => w * sb τ) x))) :
    a j = 0 := by sorry
