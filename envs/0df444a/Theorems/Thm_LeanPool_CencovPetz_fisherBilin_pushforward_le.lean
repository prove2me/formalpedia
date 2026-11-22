-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_fisherBilin_pushforward_le
-- name    : LeanPool.CencovPetz.fisherBilin_pushforward_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:22:26.82018+00:00
-- url     : https://prove2.me/theorems/8730c380-851a-4914-a5bf-64959c7068da
-- title:
--   Cencov Petz: fisher Bilin pushforward le
-- statement:
--   Monotonicity of the Fisher quadratic form under a surjective map
--   (finite sufficient statistic).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/SufficientStatistic.lean#L104-L145
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/SufficientStatistic.lean#L104-L145

module
public import Definitions.Def_LeanPool_CencovPetz_Simplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Order
public import Definitions.Def_LeanPool_CencovPetz_SufficientStatistic
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

theorem LeanPool.CencovPetz.fisherBilin_pushforward_le (g : α → β) (hg : Function.Surjective g)
    (p : Simplex α) (u : tangentSpace (α := α)) :
    fisherBilin (Simplex.pushforward (α := α) (β := β) g hg p)
        (tangentPushforward (α := α) (β := β) g u)
        (tangentPushforward (α := α) (β := β) g u)
      ≤ fisherBilin p u u := by sorry
