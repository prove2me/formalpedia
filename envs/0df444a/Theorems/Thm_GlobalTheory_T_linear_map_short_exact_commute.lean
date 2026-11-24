-- Prove2me | Theorems.Thm_GlobalTheory_T_linear_map_short_exact_commute
-- name    : GlobalTheory.T.linear_map_short_exact_commute
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:52:31.096375+00:00
-- url     : https://prove2.me/theorems/79251f02-aeb5-4c96-bed8-9a9f9c300cb0
-- title:
--   T: linear map short exact commute
-- statement:
--   The T construction uses the linear map short exact commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/LinearMapShortExactCommuteStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/LinearMapShortExactCommuteStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_LinearMapShortExactCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_LinearMapShortExactCommuteStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.linear_map_short_exact_commute : ∀ (K : Type) [Field K] (U : Type) [AddCommGroup U] [Module K U] [FiniteDimensional K U] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (i : U →ₗ[K] V) (p : V →ₗ[K] W) (a : U →ₗ[K] U) (b : V →ₗ[K] V) (c : W →ₗ[K] W), Function.Injective i → Function.Surjective p → LinearMap.range i = LinearMap.ker p → b ∘ₗ i = i ∘ₗ a → p ∘ₗ b = c ∘ₗ p → LinearMap.trace K V b = LinearMap.trace K U a + LinearMap.trace K W c := by sorry
