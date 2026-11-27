-- Prove2me | Theorems.Thm_GlobalTheory_mean_fundamentalDomain_eq_of_periodic
-- name    : GlobalTheory.mean_fundamentalDomain_eq_of_periodic
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:32.922849+00:00
-- url     : https://prove2.me/theorems/31ba20cb-ff48-5e1b-afa6-a0f8582e52c9
-- title:
--   Global Theory: mean fundamental Domain eq of periodic
-- statement:
--   The Global Theory construction uses the mean fundamental Domain eq of periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MeanFundamentalDomainEqOfPeriodic.lean#L23-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MeanFundamentalDomainEqOfPeriodic.lean#L23-L46

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MeanFundamentalDomainEqOfPeriodic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
open GlobalTheory

theorem GlobalTheory.mean_fundamentalDomain_eq_of_periodic :
    ∀ (n : Type) [Fintype n] (L L' : AddSubgroup (n → ℝ)) [Countable L] [Countable L'] (D D' : Set (n → ℝ)) (g : (n → ℝ) → ℂ), MeasureTheory.IsAddFundamentalDomain L D MeasureTheory.volume → MeasureTheory.IsAddFundamentalDomain L' D' MeasureTheory.volume → MeasureTheory.volume D < ⊤ → MeasureTheory.volume D' < ⊤ → Continuous g → (∃ C : ℝ, ∀ s, ‖g s‖ ≤ C) → (∀ p ∈ L, ∀ s, g (s + p) = g s) → (∀ p ∈ L', ∀ s, g (s + p) = g s) → ((MeasureTheory.volume D).toReal : ℂ) * ∫ s in D', g s = ((MeasureTheory.volume D').toReal : ℂ) * ∫ s in D, g s := by sorry
