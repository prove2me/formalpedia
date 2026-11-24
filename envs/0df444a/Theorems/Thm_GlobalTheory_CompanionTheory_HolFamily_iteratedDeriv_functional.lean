-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolFamily_iteratedDeriv_functional
-- name    : GlobalTheory.CompanionTheory.HolFamily.iteratedDeriv_functional
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:48:16.058396+00:00
-- url     : https://prove2.me/theorems/519a6a4c-ccaf-4ee6-a73a-6496bf4696f4
-- title:
--   Hol Family: iterated Deriv functional
-- statement:
--   The Hol Family construction uses the iterated Deriv functional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AutomorphicFunctionalHolomorphicDerivative.lean#L110-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AutomorphicFunctionalHolomorphicDerivative.lean#L110-L137

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousOnIteratedDerivFamily
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AutomorphicFunctionalHolomorphicDerivative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolFamily

theorem GlobalTheory.CompanionTheory.HolFamily.iteratedDeriv_functional {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G)
    (Lf : (G → ℂ) → ℂ)
    (hlin : ∀ (a : ℂ) (f f' : G → ℂ), Continuous f → Continuous f' →
      (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ γ ∈ Γ, ∀ g, f' (γ * g) = f' g) →
      Lf (a • f + f') = a * Lf f + Lf f')
    {C : Set G} (hC : IsCompact C)
    (hb : ∀ (f : G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) →
      (∀ x ∈ C, ‖f x‖ ≤ M) → ‖Lf f‖ ≤ M)
    {U : Set ℂ} (hU : IsOpen U) (j : ℕ) :
    ∀ E : ℂ → G → ℂ, (∀ g, DifferentiableOn ℂ (E · g) U) →
      ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ Set.univ) →
      (∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g) →
      ∀ z ∈ U, iteratedDeriv j (fun z => Lf (E z)) z = Lf fun g => iteratedDeriv j (E · g) z := by sorry
