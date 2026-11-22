-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_coarsen_pushforward_replicate
-- name    : LeanPool.CencovPetz.MarkovMorphism.coarsen_pushforward_replicate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:41.674266+00:00
-- url     : https://prove2.me/theorems/def534a3-aba0-4fec-80d7-c5fbdd435404
-- title:
--   Markov Morphism: coarsen pushforward replicate
-- statement:
--   The Markov Morphism construction uses the coarsen pushforward replicate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Replication.lean#L91-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Replication.lean#L91-L126

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

theorem LeanPool.CencovPetz.MarkovMorphism.coarsen_pushforward_replicate (m : ℕ) (hm : 0 < m) (p : Simplex α) :
    (coarsen (α := α) m hm).pushforward ((replicate (α := α) m hm).pushforward p) = p := by sorry
