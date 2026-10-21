-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_finite_collision_bound_to_exp
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.finite_collision_bound_to_exp
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:08:52.273173+00:00
-- url     : https://prove2.me/theorems/9b754a3b-4157-4f31-9cfc-dc5b8bb6da57
-- title:
--   Normalize the finite collision estimate
-- statement:
--   Given the finite collision bound and the total row-order budget, convert its factorial, row-order, and collision factors into the target exponential bound.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers

open scoped BigOperators Topology
open OAI.PiExponent.Collision
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.finite_collision_bound_to_exp
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (f : κ → ι → ℂ → ℂ)
    (center : ι → ℂ) (ell : ι → ℕ)
    {H budgetCoeff v : ℝ} (hH : 0 < H)
    (hell : ((∑ r, ell r : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v)
    (hfinite :
      ‖Matrix.det (fun r c => rowTest (ell r)
        (fun t => f (group r) c (center r + Complex.log (1 + t))))‖ ≤
        (((Fintype.card ι).factorial : ℝ) *
          Real.exp (H * budgetCoeff) ^ Fintype.card ι *
          (2 : ℝ) ^ (∑ r, ell r)) *
          Collision.collisionRatio ^
            (∑ A : κ, (((Finset.univ : Finset ι).filter
              (fun r => group r = A)).card.choose 2)) *
          ((1 - Collision.collisionRatio)⁻¹) ^ Fintype.card ι) :
      ‖Matrix.det (fun r c => rowTest (ell r)
        (fun t => f (group r) c (center r + Complex.log (1 + t))))‖ ≤
        Real.exp (-(Real.log 2 / 4) *
          (∑ A : κ,
            (((Finset.univ : Finset ι).filter (fun r => group r = A)).card : ℝ) ^ 2) +
          (Fintype.card ι : ℝ) * H *
            (budgetCoeff + Real.log 2 / v +
              Collision.collisionRemainder (Fintype.card ι) H)) := by sorry
