-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_split_pushforward_eq_uniform_of_apply_eq_div_card
-- name    : LeanPool.CencovPetz.MarkovMorphism.split_pushforward_eq_uniform_of_apply_eq_div_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:25:32.305291+00:00
-- url     : https://prove2.me/theorems/8530e916-2d8d-4cfe-a372-a2ba936b2c75
-- title:
--   Markov Morphism: split pushforward eq uniform of apply eq div card
-- statement:
--   The Markov Morphism construction uses the split pushforward eq uniform of apply eq div card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/SplittingUniform.lean#L59-L73
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/SplittingUniform.lean#L59-L73

module
public import Definitions.Def_LeanPool_CencovPetz_Splitting
public import Definitions.Def_LeanPool_CencovPetz_UniformSimplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_SplittingUniform
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
open LeanPool.CencovPetz.MarkovMorphism
variable {α : Type u} [Fintype α] [Nonempty α]

theorem LeanPool.CencovPetz.MarkovMorphism.split_pushforward_eq_uniform_of_apply_eq_div_card (m : α → ℕ) (hm : ∀ a, 0 < m a)
    (p : Simplex α)
    (hp : ∀ a, p.p a = (m a : ℝ) / (Fintype.card (SplitTarget (α := α) m) : ℝ)) :
    letI : Nonempty (SplitTarget (α := α) m) := by
      classical
      rcases (inferInstance : Nonempty α) with ⟨a0⟩
      exact ⟨⟨a0, ⟨0, hm a0⟩⟩⟩
    (split (α := α) m hm).pushforward p = Simplex.uniform (α := SplitTarget (α := α) m) := by sorry
