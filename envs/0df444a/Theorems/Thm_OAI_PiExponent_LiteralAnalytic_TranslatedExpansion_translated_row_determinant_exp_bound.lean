-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_translated_row_determinant_exp_bound
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.translated_row_determinant_exp_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T07:51:37.805805+00:00
-- url     : https://prove2.me/theorems/8d6245b1-8825-4d92-bcec-d4f5ce9229a3
-- title:
--   Analytic collision bound for translated row determinants
-- statement:
--   A determinant of row tests of holomorphic columns, translated by group-dependent centers, has an exponential bound with a negative squared-multiplicity term. The remaining exponent depends on a uniform disk bound, the total row order, and the collision remainder.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers

open scoped BigOperators Topology
open OAI.PiExponent.Collision
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.translated_row_determinant_exp_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (f : κ → ι → ℂ → ℂ)
    (center : ι → ℂ) (ell : ι → ℕ)
    (R : NNReal) (hR : 0 < R) {H budgetCoeff v : ℝ} (hH : 0 < H)
    (hf : ∀ A c, Differentiable ℂ (f A c))
    (hfD : ∀ A c z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) →
      ‖f A c z‖ ≤ Real.exp (H * budgetCoeff))
    (hc : ∀ r, ‖center r‖ + 3 / 4 ≤ (R : ℝ) / 2)
    (hell : ((∑ r, ell r : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v) :
    ‖Matrix.det (fun r c => rowTest (ell r)
      (fun t => f (group r) c (center r + Complex.log (1 + t))))‖ ≤
      Real.exp (-(Real.log 2 / 4) *
        (∑ A : κ,
          (((Finset.univ : Finset ι).filter (fun r => group r = A)).card : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H *
          (budgetCoeff + Real.log 2 / v +
            Collision.collisionRemainder (Fintype.card ι) H)) := by sorry
