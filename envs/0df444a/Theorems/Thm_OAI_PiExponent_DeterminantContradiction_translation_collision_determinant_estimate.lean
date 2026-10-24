-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_collision_determinant_estimate
-- name    : OAI.PiExponent.DeterminantContradiction.translation_collision_determinant_estimate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T22:59:01.0311+00:00
-- url     : https://prove2.me/theorems/afda5c5a-4b29-41a4-a248-f28c4efeb500
-- title:
--   Collision estimate for a translated formal-period determinant
-- statement:
--   Port LiteralAnalyticSummand.norm_choiceMatrix_le via Collision.formal_period_collision_bound. Identify formal-period coefficients with Taylor coefficients of entire exponential-polynomial column functions. Use the weighted column bound on radius 100K, Cauchy's inequality, and the collision determinant estimate grouped by transverse index. Retain squared multiplicities and the complete logarithmic remainder. Natural subtraction s−k is valid because RowChoice enforces k≤s; its total is bounded by M H/v0. FixedData supplies positivity of K,w0,v0,wstar, and H>0 is explicit. This analytic obligation is independent of the scalar approximation estimate and needs neither injective selection nor nonzero determinant.

import Definitions.Def_OAI_PiExponent_MinorTranslationData
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.translation_collision_determinant_estimate
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖(choiceMatrix d selection f).det‖ ≤ Real.exp
      (-(Real.log 2 / 4) * (∑ A : Transverse d H,
        (multiplicity (fun r : Row d H => (f r).1) A : ℝ) ^ 2) +
        (actualRowCount d H : ℝ) * H *
          (d.holomorphicError + remainder (actualRowCount d H) H)) := by sorry
