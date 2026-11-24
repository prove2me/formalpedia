-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolFamily_continuous_iteratedDeriv_family
-- name    : GlobalTheory.CompanionTheory.HolFamily.continuous_iteratedDeriv_family
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:48:48.526164+00:00
-- url     : https://prove2.me/theorems/33627b8b-a459-43fc-aa46-b3f232f68c9f
-- title:
--   Hol Family: continuous iterated Deriv family
-- statement:
--   The Hol Family construction uses the continuous iterated Deriv family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousIteratedDerivHolomorphicFamily.lean#L7-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousIteratedDerivHolomorphicFamily.lean#L7-L54

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousIteratedDerivHolomorphicFamily
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

theorem GlobalTheory.CompanionTheory.HolFamily.continuous_iteratedDeriv_family :
    ∀ {G : Type} [TopologicalSpace G] (U : Set ℂ) (Ê : ℂ → G → ℂ), IsOpen U →
      (∀ g, DifferentiableOn ℂ (Ê · g) U) →
      ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) →
      ∀ z ∈ U, ∀ j : ℕ, Continuous fun g => iteratedDeriv j (Ê · g) z := by sorry
