-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_coarsen_tangentPushforward_replicate
-- name    : LeanPool.CencovPetz.MarkovMorphism.coarsen_tangentPushforward_replicate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:46.067946+00:00
-- url     : https://prove2.me/theorems/4cf18013-c33c-4d70-a088-b3c0e67e6805
-- title:
--   Markov Morphism: coarsen tangent Pushforward replicate
-- statement:
--   The Markov Morphism construction uses the coarsen tangent Pushforward replicate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Replication.lean#L128-L161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Replication.lean#L128-L161

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

theorem LeanPool.CencovPetz.MarkovMorphism.coarsen_tangentPushforward_replicate (m : ℕ) (hm : 0 < m)
    (u : tangentSpace (α := α)) :
    (coarsen (α := α) m hm).tangentPushforward
      ((replicate (α := α) m hm).tangentPushforward u) = u := by sorry
