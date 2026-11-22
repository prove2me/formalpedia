-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_card_splitTarget
-- name    : LeanPool.CencovPetz.MarkovMorphism.card_splitTarget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:53.771538+00:00
-- url     : https://prove2.me/theorems/76645646-f24a-429d-a359-c315eaf1e112
-- title:
--   Markov Morphism: card split Target
-- statement:
--   The Markov Morphism construction uses the card split Target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/RationalPoint.lean#L48-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/RationalPoint.lean#L48-L51

module
public import Definitions.Def_LeanPool_CencovPetz_SplittingUniform
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_RationalPoint
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
open LeanPool.CencovPetz.MarkovMorphism
variable {α : Type u} [Fintype α]

theorem LeanPool.CencovPetz.MarkovMorphism.card_splitTarget (m : α → ℕ) :
    Fintype.card (SplitTarget (α := α) m) = ∑ a : α, m a := by sorry
