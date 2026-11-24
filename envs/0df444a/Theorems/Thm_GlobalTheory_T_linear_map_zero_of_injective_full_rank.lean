-- Prove2me | Theorems.Thm_GlobalTheory_T_linear_map_zero_of_injective_full_rank
-- name    : GlobalTheory.T.linear_map_zero_of_injective_full_rank
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:52:52.749801+00:00
-- url     : https://prove2.me/theorems/3607292a-e860-48cf-8ae6-2ce2479b4cec
-- title:
--   T: linear map zero of injective full rank
-- statement:
--   The T construction uses the linear map zero of injective full rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LinearMapZeroOfInjectiveFullRankStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LinearMapZeroOfInjectiveFullRankStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LinearMapZeroOfInjectiveFullRank
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LinearMapZeroOfInjectiveFullRankStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.linear_map_zero_of_injective_full_rank : ∀ (A W N : Type) [CommRing A] [Nontrivial A] [AddCommGroup W] [Module A W] [AddCommGroup N] [Module A N] [Module.Free A W] [Module.Finite A W] [Module.Free A N] (g : ℕ) (φ : (Fin g → A) →ₗ[A] W) (f : W →ₗ[A] N), Module.finrank A W = g → Function.Injective φ → f ∘ₗ φ = 0 → f = 0 := by sorry
