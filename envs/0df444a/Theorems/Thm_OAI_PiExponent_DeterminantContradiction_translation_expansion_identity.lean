-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_expansion_identity
-- name    : OAI.PiExponent.DeterminantContradiction.translation_expansion_identity
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T22:58:05.704892+00:00
-- url     : https://prove2.me/theorems/a9d3cfea-d748-479a-aa53-c6e3d31c2ce2
-- title:
--   Exact selected-minor expansion over finite row translations
-- statement:
--   Port AnalyticAggregate.actual_minor_expansion through the staged definitions. Write the truncated logarithm as the full logarithm plus its signed tail, expand transverse monomials by the binomial theorem, convolve coefficients, and use determinant multilinearity in rows. This removes the finite algebraic expansion independently of analytic estimates. The coefficient index ranges from zero through the row order. No positivity or nonvanishing is needed; empty row sets give 1 on both sides.

import Definitions.Def_OAI_PiExponent_MinorTranslationData
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.translation_expansion_identity
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (selection : Row d H → Column d H) :
    (actualMinor d H selection).det =
      ∑ f : ChoiceFamily d H, (∏ r, choiceScalar d r (f r)) *
        (choiceMatrix d selection f).det := by sorry
