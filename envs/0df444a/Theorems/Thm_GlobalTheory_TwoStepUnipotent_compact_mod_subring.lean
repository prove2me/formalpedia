-- Prove2me | Theorems.Thm_GlobalTheory_TwoStepUnipotent_compact_mod_subring
-- name    : GlobalTheory.TwoStepUnipotent.compact_mod_subring
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:16:47.688291+00:00
-- url     : https://prove2.me/theorems/28df2631-431b-4f12-be98-ab793ca41bc7
-- title:
--   Two Step Unipotent: compact mod subring
-- statement:
--   The Two Step Unipotent construction uses the compact mod subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/TwoStepUnipotentCompactModSubring.lean#L226-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/TwoStepUnipotentCompactModSubring.lean#L226-L346

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_TwoStepUnipotentCompactModSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory GlobalTheory.TwoStepUnipotent

theorem GlobalTheory.TwoStepUnipotent.compact_mod_subring (S : Type) [Ring S] [TopologicalSpace S] [IsTopologicalRing S]
    (st : S →+ S) (S₀ : Subring S) (e₁ e₃ h : S) (K : Set S) (hcont : Continuous st)
    (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (h0 : ∀ x ∈ S₀, st x ∈ S₀) (he : e₁ ∈ S₀) (hh0 : h ∈ S₀) (h11 : e₁ * e₁ = e₁)
    (hs : st e₁ = e₃) (h13 : e₁ * e₃ = 0) (h31 : e₃ * e₁ = 0) (hh : h + h = 1)
    (hc : ∀ x, h * x = x * h) (hK : IsCompact K) (hcov : ∀ x, ∃ y ∈ S₀, x - y ∈ K) :
    ∃ K' : Set Sˣ, IsCompact K' ∧ (∀ g ∈ K', (st (g : S) * (g : S) = 1 ∧ ((g : S) - 1) * e₁ = 0 ∧
      (1 - e₁) * ((g : S) - 1) * (1 - e₃) = 0)) ∧ ∀ g : Sˣ, (st (g : S) * (g : S) = 1 ∧
      ((g : S) - 1) * e₁ = 0 ∧ (1 - e₁) * ((g : S) - 1) * (1 - e₃) = 0) →
      ∃ γ : Sˣ, (st (γ : S) * (γ : S) = 1 ∧ ((γ : S) - 1) * e₁ = 0 ∧
      (1 - e₁) * ((γ : S) - 1) * (1 - e₃) = 0) ∧ (γ : S) ∈ S₀ ∧ ((γ⁻¹ : Sˣ) : S) ∈ S₀ ∧
      γ * g ∈ K' := by sorry
