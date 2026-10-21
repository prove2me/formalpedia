-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_finite_collision_scalar_normalization
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.finite_collision_scalar_normalization
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T13:16:09.375868+00:00
-- url     : https://prove2.me/theorems/36bb3b6d-eab0-49d0-83bc-58e81523a4e4
-- title:
--   Normalize the finite collision factors
-- statement:
--   Under the total row-order budget, bound the factorial, row-order, collision, and inverse-collision factors by the exponential expression used in the target.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers

open scoped BigOperators Topology
open OAI.PiExponent.Collision
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.finite_collision_scalar_normalization
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (ell : ι → ℕ)
    {H budgetCoeff v : ℝ} (hH : 0 < H)
    (hell : ((∑ r, ell r : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v) :
    (((Fintype.card ι).factorial : ℝ) *
      Real.exp (H * budgetCoeff) ^ Fintype.card ι *
      (2 : ℝ) ^ (∑ r, ell r)) *
      Collision.collisionRatio ^
        (∑ A : κ, (((Finset.univ : Finset ι).filter
          (fun r => group r = A)).card.choose 2)) *
      ((1 - Collision.collisionRatio)⁻¹) ^ Fintype.card ι ≤
    Real.exp (-(Real.log 2 / 4) *
      (∑ A : κ,
        (((Finset.univ : Finset ι).filter (fun r => group r = A)).card : ℝ) ^ 2) +
      (Fintype.card ι : ℝ) * H *
        (budgetCoeff + Real.log 2 / v +
          Collision.collisionRemainder (Fintype.card ι) H)) := by sorry
