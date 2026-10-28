-- Prove2me | Theorems.Thm_OAI_MomentSchauder_smooth_of_regular_three
-- name    : OAI.MomentSchauder.smooth_of_regular_three
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T05:15:55.179511+00:00
-- url     : https://prove2.me/theorems/55ff09c2-32a7-41b2-9cad-b26e5c421454
-- title:
--   OAI.MomentSchauder.smooth_of_regular_three: intermediate lemma from OpenAI, The logarithmic Brunn–Minkowski conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogBrunnMinkowski.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The logarithmic Brunn–Minkowski conjecture*, OpenAI Math Release, September 23, 2026, result family 91, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MomentSchauder.smooth_of_regular_three` of [lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MomentSchauder`, with `open Set Metric Matrix InnerProductSpace HolderJets MomentQuotient`, `open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise`):
--
--   ```lean
--   theorem smooth_of_regular_three (μ:MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
--       (b:OrthonormalBasis ι ℝ E) {u V:E→ℝ} (hu:Regular 3 u) (hV:ContDiff ℝ ∞ V)
--       {d:ℝ} (heq:∀x,Real.log (matrixHessian b u x).det=V (gradient u x)+d-u x)
--       (hp:∀x,(matrixHessian b u x).PosDef) : ContDiff ℝ ∞ u
--   ```
--
--   **Definitions.** The statement is written with `OAI.HolderJets.Regular` and `OAI.MomentQuotient.matrixHessian` (definitions bundle `OAIW2LB000` of this split).
--
--   **Used by.** The proof of `OAI.LogBrunnMinkowski.softVariance` of this split imports it.
-- source:
--   OpenAI, The logarithmic Brunn–Minkowski conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 91; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean (declaration OAI.MomentSchauder.smooth_of_regular_three)

import Mathlib
import Definitions.Def_OAIW2LB000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MomentSchauder
open Set Metric Matrix InnerProductSpace HolderJets MomentQuotient
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
variable {E:Type} {ι:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι]
local notation "Hes" => HessianInterpolation.hessian

theorem smooth_of_regular_three (μ:MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (b:OrthonormalBasis ι ℝ E) {u V:E→ℝ} (hu:Regular 3 u) (hV:ContDiff ℝ ∞ V)
    {d:ℝ} (heq:∀x,Real.log (matrixHessian b u x).det=V (gradient u x)+d-u x)
    (hp:∀x,(matrixHessian b u x).PosDef) : ContDiff ℝ ∞ u := by
  sorry

end MomentSchauder

end

end OAI
end
