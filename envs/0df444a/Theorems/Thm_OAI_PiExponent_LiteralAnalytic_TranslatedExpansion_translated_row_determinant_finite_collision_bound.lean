-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_translated_row_determinant_finite_collision_bound
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.translated_row_determinant_finite_collision_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:08:22.139008+00:00
-- url     : https://prove2.me/theorems/918b1338-54c3-4d62-92ec-3568dec895b6
-- title:
--   Finite collision estimate for translated row determinants
-- statement:
--   Under the holomorphicity, disk bound, and center hypotheses, the translated row-test determinant is bounded by a finite product of a factorial factor, the uniform analytic bound, row-order costs, a group collision penalty, and a geometric-tail factor.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers

open scoped BigOperators Topology
open OAI.PiExponent.Collision
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.translated_row_determinant_finite_collision_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (f : κ → ι → ℂ → ℂ)
    (center : ι → ℂ) (ell : ι → ℕ)
    (R : NNReal) (hR : 0 < R) {H budgetCoeff : ℝ}
    (hf : ∀ A c, Differentiable ℂ (f A c))
    (hfD : ∀ A c z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) →
      ‖f A c z‖ ≤ Real.exp (H * budgetCoeff))
    (hc : ∀ r, ‖center r‖ + 3 / 4 ≤ (R : ℝ) / 2) :
    ‖Matrix.det (fun r c => rowTest (ell r)
      (fun t => f (group r) c (center r + Complex.log (1 + t))))‖ ≤
      (((Fintype.card ι).factorial : ℝ) *
        Real.exp (H * budgetCoeff) ^ Fintype.card ι *
        (2 : ℝ) ^ (∑ r, ell r)) *
        Collision.collisionRatio ^
          (∑ A : κ, (((Finset.univ : Finset ι).filter
            (fun r => group r = A)).card.choose 2)) *
        ((1 - Collision.collisionRatio)⁻¹) ^ Fintype.card ι := by sorry
