-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_merge_tangentPushforward_split
-- name    : LeanPool.CencovPetz.MarkovMorphism.merge_tangentPushforward_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:44.40841+00:00
-- url     : https://prove2.me/theorems/4be0c14a-2b77-417f-a216-6dbe802bed11
-- title:
--   Markov Morphism: merge tangent Pushforward split
-- statement:
--   The Markov Morphism construction uses the merge tangent Pushforward split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Splitting.lean#L146-L188
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Splitting.lean#L146-L188

module
public import Definitions.Def_LeanPool_CencovPetz_MarkovMorphism
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_Splitting
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
open LeanPool.CencovPetz.MarkovMorphism
variable {α : Type u} [Fintype α]
variable (m : α → ℕ) (hm : ∀ a, 0 < m a)

theorem LeanPool.CencovPetz.MarkovMorphism.merge_tangentPushforward_split (u : tangentSpace (α := α)) :
    (merge (α := α) m hm).tangentPushforward ((split (α := α) m hm).tangentPushforward u) = u := by sorry
