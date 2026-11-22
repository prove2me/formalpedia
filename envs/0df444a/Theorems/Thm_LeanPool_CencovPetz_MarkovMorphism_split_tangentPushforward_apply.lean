-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_split_tangentPushforward_apply
-- name    : LeanPool.CencovPetz.MarkovMorphism.split_tangentPushforward_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:47.914697+00:00
-- url     : https://prove2.me/theorems/68e19e08-771c-4c4a-86b3-95efe8367eab
-- title:
--   Markov Morphism: split tangent Pushforward apply
-- statement:
--   The Markov Morphism construction uses the split tangent Pushforward apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Splitting.lean#L100-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Splitting.lean#L100-L104

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

theorem LeanPool.CencovPetz.MarkovMorphism.split_tangentPushforward_apply (u : tangentSpace (α := α)) (a : α) (i : Fin (m a)) :
    (((split (α := α) m hm).tangentPushforward u : SplitTarget (α := α) m → ℝ) ⟨a, i⟩)
      = (u : α → ℝ) a / (m a : ℝ) := by sorry
