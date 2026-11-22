-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_replicate_tangentPushforward_apply
-- name    : LeanPool.CencovPetz.MarkovMorphism.replicate_tangentPushforward_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:45.010659+00:00
-- url     : https://prove2.me/theorems/d8cf6b4b-a379-4403-b391-e0dcdad1fe6b
-- title:
--   Markov Morphism: replicate tangent Pushforward apply
-- statement:
--   The Markov Morphism construction uses the replicate tangent Pushforward apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Replication.lean#L77-L82
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Replication.lean#L77-L82

module
public import Definitions.Def_LeanPool_CencovPetz_MarkovMorphism
public import Definitions.Def_LeanPool_CencovPetz_UniformSimplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_Replication
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {α : Type u} [Fintype α]
open LeanPool.CencovPetz.MarkovMorphism

theorem LeanPool.CencovPetz.MarkovMorphism.replicate_tangentPushforward_apply (m : ℕ) (hm : 0 < m)
    (u : tangentSpace (α := α)) (a : α) (i : Fin m) :
    ((replicate (α := α) m hm).tangentPushforward u : α × Fin m → ℝ) (a, i) =
      (u : α → ℝ) a / m := by sorry
