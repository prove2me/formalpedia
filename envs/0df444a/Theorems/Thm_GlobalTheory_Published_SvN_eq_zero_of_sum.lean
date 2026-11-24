-- Prove2me | Theorems.Thm_GlobalTheory_Published_SvN_eq_zero_of_sum
-- name    : GlobalTheory.Published.SvN.eq_zero_of_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:58:02.822645+00:00
-- url     : https://prove2.me/theorems/df3083f8-1dcb-4353-a7ff-4a108acbbe36
-- title:
--   Sv N: eq zero of sum
-- statement:
--   The Sv N construction uses the eq zero of sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L209-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L209-L225

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
variable {W M : Type} [AddCommGroup W] [AddCommGroup M] [Module ℂ M]
variable {c : W → W → ℂ}
variable {ρ : W → Module.End ℂ M}
variable {A : AddSubgroup W} {α : W → ℂ}

theorem GlobalTheory.Published.SvN.eq_zero_of_sum {ι : Type} (s : Finset ι) (β : ι → W → ℂ) (hβ : ∀ i, ∃ a ∈ A, β i a ≠ α a) :
    ∀ (m : ι → M), (∀ i, ∀ a ∈ A, ρ a (m i) = β i a • m i) →
      (∀ a ∈ A, ρ a (∑ i ∈ s, m i) = α a • ∑ i ∈ s, m i) → ∑ i ∈ s, m i = 0 := by sorry
