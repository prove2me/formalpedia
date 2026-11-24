-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisCross_stage_eis
-- name    : GlobalTheory.CompanionTheory.RgEisCross.stage_eis
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:57:36.269704+00:00
-- url     : https://prove2.me/theorems/009b01ba-2d08-44ac-8ad0-eeb361e65b91
-- title:
--   Rg Eis Cross: stage eis
-- statement:
--   The Rg Eis Cross construction uses the stage eis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SectionInvarianceCosetSum.lean#L9-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SectionInvarianceCosetSum.lean#L9-L40

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SectionInvarianceCosetSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisCross
open PositivityTheory.RgEis

theorem GlobalTheory.CompanionTheory.RgEisCross.stage_eis : PositivityTheory.RgEis.PiLocalization₂ → ∀ (G : Type) [Group G] (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (Γ K Q P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (ξ lam : G → ℝ) (Λ : G → ℂ) (s : ℂ) (w : W) (Ms : ℝ),
    P ≤ Q → (∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x) → (∀ γ ∈ Γ, γ ∈ P → ∀ x, Λ (γ * x) = Λ x) →
    (∀ γ ∈ Γ, γ ∈ P → ∀ x, PositivityTheory.RgEis.sec K P c ρ (γ * x) w = PositivityTheory.RgEis.sec K P c ρ x w) →
    (∀ x, ‖PositivityTheory.RgEis.sec K P c ρ x w‖ ≤ Ms) → PositivityTheory.RgEis.Conv Γ P lam →
    (∀ x, (Λ x + s * ξ x).re = lam x) → ∀ g : G,
    ∑' r : PositivityTheory.RgEis.Cos (Γ ⊓ Q) Γ, Complex.exp (s * ξ (PositivityTheory.RgEis.rep r * g)) •
        PositivityTheory.RgEis.eis (Γ ⊓ Q) K P c ρ Λ (PositivityTheory.RgEis.rep r * g) w =
      PositivityTheory.RgEis.eis Γ K P c ρ (fun x => Λ x + s * ξ x) g w := by sorry
