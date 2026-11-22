-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_replicate_pushforward_uniform
-- name    : LeanPool.CencovPetz.MarkovMorphism.replicate_pushforward_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:44.778266+00:00
-- url     : https://prove2.me/theorems/6ca5e238-466c-402d-8dcc-8ffaffbcada8
-- title:
--   Markov Morphism: replicate pushforward uniform
-- statement:
--   The Markov Morphism construction uses the replicate pushforward uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Replication.lean#L63-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Replication.lean#L63-L75

module
public import Definitions.Def_LeanPool_CencovPetz_MarkovMorphism
public import Definitions.Def_LeanPool_CencovPetz_UniformSimplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_Replication
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_Simplex_uniform_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
attribute [local simp] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
attribute [local simp] LeanPool.CencovPetz.Simplex.uniform_apply
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {α : Type u} [Fintype α]
open LeanPool.CencovPetz.MarkovMorphism

theorem LeanPool.CencovPetz.MarkovMorphism.replicate_pushforward_uniform [Nonempty α] (m : ℕ) (hm : 0 < m) :
    letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    letI : Nonempty (α × Fin m) := by
        simp_all
    (replicate (α := α) m hm).pushforward (Simplex.uniform (α := α))
      =
      Simplex.uniform (α := α × Fin m) := by sorry
