-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FormalAlg_Lift_SerreSat_saturated_fg_of_powerTorsion_ker_coker
-- name    : GlobalTheory.CompanionTheory.FormalAlg.Lift.SerreSat.saturated_fg_of_powerTorsion_ker_coker
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:38:35.671184+00:00
-- url     : https://prove2.me/theorems/4139821e-116a-4c69-b63f-6598c747b85c
-- title:
--   Serre Sat: saturated fg of power Torsion ker coker
-- statement:
--   The Serre Sat construction uses the saturated fg of power Torsion ker coker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SaturatedFgOfPowerTorsionKerCoker.lean#L5-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SaturatedFgOfPowerTorsionKerCoker.lean#L5-L45

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SaturatedFgOfPowerTorsionKerCoker
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift GlobalTheory.CompanionTheory.FormalAlg.Lift.SerreSat

theorem GlobalTheory.CompanionTheory.FormalAlg.Lift.SerreSat.saturated_fg_of_powerTorsion_ker_coker :
    ∀ (B : Type) [CommRing B] (x : B) (M N : Type) [AddCommGroup M] [Module B M]
      [AddCommGroup N] [Module B N] (e : M →ₗ[B] N),
      (∀ m, e m = 0 → ∃ l : ℕ, x ^ l • m = 0) →
      (∀ f, ∃ (l : ℕ) (m : M), e m = x ^ l • f) →
      (∃ s : Finset N, ∀ f : N, ∃ k : ℕ, x ^ k • f ∈ Submodule.span B (s : Set N)) →
      ∃ T : Finset M, ∀ m : M, ∃ k : ℕ, x ^ k • m ∈ Submodule.span B (T : Set M) := by sorry
