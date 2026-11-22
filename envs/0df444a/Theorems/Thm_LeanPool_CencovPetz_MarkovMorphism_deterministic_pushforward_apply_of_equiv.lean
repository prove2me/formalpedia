-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_deterministic_pushforward_apply_of_equiv
-- name    : LeanPool.CencovPetz.MarkovMorphism.deterministic_pushforward_apply_of_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:25:49.097196+00:00
-- url     : https://prove2.me/theorems/19ec5480-e256-4c73-b868-d88337f7013b
-- title:
--   Markov Morphism: deterministic pushforward apply of equiv
-- statement:
--   The Markov Morphism construction uses the deterministic pushforward apply of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariance.lean#L62-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariance.lean#L62-L81

module
public import Definitions.Def_LeanPool_CencovPetz_SufficientStatistic
public import Definitions.Def_LeanPool_CencovPetz_MonotoneMetric
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Definitions.Def_LeanPool_CencovPetz_LeftInverseIsometry
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariance
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {α β : Type u} [Fintype α] [Fintype β]
open LeanPool.CencovPetz.MarkovMorphism

theorem LeanPool.CencovPetz.MarkovMorphism.deterministic_pushforward_apply_of_equiv
    (e : α ≃ β) (p : Simplex α) (b : β) :
    ((MarkovMorphism.deterministic (α := α) (β := β)
        (g := (e : α → β)) e.surjective).pushforward
        p).p b =
      p.p (e.symm b) := by sorry
