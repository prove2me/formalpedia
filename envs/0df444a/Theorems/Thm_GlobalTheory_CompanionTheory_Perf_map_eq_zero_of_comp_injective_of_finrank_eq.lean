-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Perf_map_eq_zero_of_comp_injective_of_finrank_eq
-- name    : GlobalTheory.CompanionTheory.Perf.map_eq_zero_of_comp_injective_of_finrank_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:54:09.662015+00:00
-- url     : https://prove2.me/theorems/def65c1a-522a-4177-ab46-4dc25d66f9a1
-- title:
--   Perf: map eq zero of comp injective of finrank eq
-- statement:
--   The Perf construction uses the map eq zero of comp injective of finrank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LinearMapZeroOfInjectiveFullRank.lean#L6-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LinearMapZeroOfInjectiveFullRank.lean#L6-L39

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LinearMapZeroOfInjectiveFullRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Perf

theorem GlobalTheory.CompanionTheory.Perf.map_eq_zero_of_comp_injective_of_finrank_eq :
    ∀ (A W N : Type) [CommRing A] [Nontrivial A] [AddCommGroup W] [Module A W] [AddCommGroup N]
      [Module A N] [Module.Free A W] [Module.Finite A W] [Module.Free A N] (g : ℕ)
      (φ : (Fin g → A) →ₗ[A] W) (f : W →ₗ[A] N),
      Module.finrank A W = g → Function.Injective φ → f ∘ₗ φ = 0 → f = 0 := by sorry
