-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_deterministic_pushforward_eq_simplex_pushforward
-- name    : LeanPool.CencovPetz.MarkovMorphism.deterministic_pushforward_eq_simplex_pushforward
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:25:51.959377+00:00
-- url     : https://prove2.me/theorems/8297c6ea-1e18-4b48-b314-d65125a43ce7
-- title:
--   Markov Morphism: deterministic pushforward eq simplex pushforward
-- statement:
--   The Markov Morphism construction uses the deterministic pushforward eq simplex pushforward property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariance.lean#L45-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariance.lean#L45-L51

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

theorem LeanPool.CencovPetz.MarkovMorphism.deterministic_pushforward_eq_simplex_pushforward [DecidableEq β] (g : α → β)
    (hg : Function.Surjective g) (p : Simplex α) :
    (MarkovMorphism.deterministic (α := α) (β := β) g hg).pushforward p =
      Simplex.pushforward (α := α) (β := β) g hg p := by sorry
