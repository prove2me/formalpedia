-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_fisherBilin_pushforward_le_of_markovMorphism
-- name    : LeanPool.CencovPetz.fisherBilin_pushforward_le_of_markovMorphism
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:22:28.518672+00:00
-- url     : https://prove2.me/theorems/f681bd9f-be33-4367-9a82-6e8841a55e39
-- title:
--   Cencov Petz: fisher Bilin pushforward le of markov Morphism
-- statement:
--   Fisher monotonicity under a finite Markov morphism.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/MarkovMorphism.lean#L197-L281
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/MarkovMorphism.lean#L197-L281

module
public import Definitions.Def_LeanPool_CencovPetz_Simplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Order
public import Definitions.Def_LeanPool_CencovPetz_MarkovMorphism
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]

theorem LeanPool.CencovPetz.fisherBilin_pushforward_le_of_markovMorphism (κ : MarkovMorphism α β)
    (p : Simplex α) (u : tangentSpace (α := α)) :
    fisherBilin (κ.pushforward p) (κ.tangentPushforward u) (κ.tangentPushforward u) ≤
      fisherBilin p u u := by sorry
