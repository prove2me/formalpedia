-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_Simplex_IsRational_isSplitRepresentable
-- name    : LeanPool.CencovPetz.Simplex.IsRational.isSplitRepresentable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:25:58.959474+00:00
-- url     : https://prove2.me/theorems/55e7e0af-2e65-488c-9962-5ed38846f373
-- title:
--   Is Rational: is Split Representable
-- statement:
--   The Is Rational construction uses the is Split Representable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/RationalPoint.lean#L66-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/RationalPoint.lean#L66-L70

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
open LeanPool.CencovPetz.Simplex
variable {α : Type u} [Fintype α]

theorem LeanPool.CencovPetz.Simplex.IsRational.isSplitRepresentable {p : Simplex α} (hp : IsRational (α := α) p) :
    IsSplitRepresentable (α := α) p := by sorry
