-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_Simplex_dense_setOf_isRational
-- name    : LeanPool.CencovPetz.Simplex.dense_setOf_isRational
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:57.148189+00:00
-- url     : https://prove2.me/theorems/4ba73d89-c6e1-4cd2-946e-e18879900195
-- title:
--   Simplex: dense set Of is Rational
-- statement:
--   The Simplex construction uses the dense set Of is Rational property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/RationalDensity.lean#L268-L274
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/RationalDensity.lean#L268-L274

module
public import Definitions.Def_LeanPool_CencovPetz_RationalPoint
public import Definitions.Def_LeanPool_CencovPetz_SimplexTopology
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Definitions.Def_LeanPool_CencovPetz_RationalDensity
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
open LeanPool.CencovPetz.Simplex
open Filter Topology
variable {α : Type*} [Fintype α]
noncomputable section
variable [Nonempty α]

theorem LeanPool.CencovPetz.Simplex.dense_setOf_isRational : Dense {p : Simplex α | IsRational (α := α) p} := by sorry
