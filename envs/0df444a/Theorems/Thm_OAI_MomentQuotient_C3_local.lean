-- Prove2me | Theorems.Thm_OAI_MomentQuotient_C3_local
-- name    : OAI.MomentQuotient.C3_local
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T05:14:45.428982+00:00
-- url     : https://prove2.me/theorems/644a769c-d1dd-46e3-a6c5-215902cabf67
-- title:
--   OAI.MomentQuotient.C3_local: intermediate lemma from OpenAI, The logarithmic Brunn–Minkowski conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogBrunnMinkowski.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The logarithmic Brunn–Minkowski conjecture*, OpenAI Math Release, September 23, 2026, result family 91, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MomentQuotient.C3_local` of [lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MomentQuotient`, with `open Set Metric InnerProductSpace`, `open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise`):
--
--   ```lean
--   theorem C3_local (μ:MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
--       (b:OrthonormalBasis ι ℝ E) {u V:E→ℝ} (hu:ContDiff ℝ 2 u) (hV:ContDiff ℝ 2 V)
--       {d:ℝ} (heq:∀x,Real.log (matrixHessian b u x).det=V (gradient u x)+d-u x)
--       (hp:∀x,(matrixHessian b u x).PosDef) {a C R:ℝ} {c:E}
--       (ha:0<a) (ha1:a<1) (hC:0≤C) (hR:0<R)
--       (hhold:∀x∈ball c R,∀y∈ball c R,dist (matrixHessian b u x) (matrixHessian b u y)≤C*dist x y^a) :
--       ∃r:ℝ,0<r ∧ ContDiffOn ℝ 3 u (ball c r) ∧
--         ∃U:ℝ,0≤U ∧ ∀x∈ball c r,∀y∈ball c r,
--           dist (fderiv ℝ (HessianInterpolation.hessian u) x)
--             (fderiv ℝ (HessianInterpolation.hessian u) y)≤U*dist x y^a
--   ```
--
--   **Definitions.** The statement is written with `OAI.HessianInterpolation.hessian`, `OAI.MomentQuotient.instNormedAddCommGroupContinuousLinearMapRealId_solutions_2`, `OAI.MomentQuotient.instNormedSpaceRealContinuousLinearMapId_solutions_2`, `OAI.MomentQuotient.instNormedSpaceRealContinuousLinearMapId_solutions_3` and `OAI.MomentQuotient.matrixHessian` (definitions bundle `OAIW2LB000` of this split).
--
--   **Used by.** The proof of `OAI.LogBrunnMinkowski.softVariance` of this split imports it.
-- source:
--   OpenAI, The logarithmic Brunn–Minkowski conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 91; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean (declaration OAI.MomentQuotient.C3_local)

import Mathlib
import Definitions.Def_OAIW2LB000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MomentQuotient
open Set Metric InnerProductSpace
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
variable {E : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.MomentQuotient.instNormedAddCommGroupContinuousLinearMapRealId_solutions_2
attribute [local instance] OAI.MomentQuotient.instNormedSpaceRealContinuousLinearMapId_solutions_2
attribute [local instance] OAI.MomentQuotient.instNormedAddCommGroupContinuousLinearMapRealId_solutions_3
attribute [local instance] OAI.MomentQuotient.instNormedSpaceRealContinuousLinearMapId_solutions_3
theorem C3_local (μ:MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (b:OrthonormalBasis ι ℝ E) {u V:E→ℝ} (hu:ContDiff ℝ 2 u) (hV:ContDiff ℝ 2 V)
    {d:ℝ} (heq:∀x,Real.log (matrixHessian b u x).det=V (gradient u x)+d-u x)
    (hp:∀x,(matrixHessian b u x).PosDef) {a C R:ℝ} {c:E}
    (ha:0<a) (ha1:a<1) (hC:0≤C) (hR:0<R)
    (hhold:∀x∈ball c R,∀y∈ball c R,dist (matrixHessian b u x) (matrixHessian b u y)≤C*dist x y^a) :
    ∃r:ℝ,0<r ∧ ContDiffOn ℝ 3 u (ball c r) ∧
      ∃U:ℝ,0≤U ∧ ∀x∈ball c r,∀y∈ball c r,
        dist (fderiv ℝ (HessianInterpolation.hessian u) x)
          (fderiv ℝ (HessianInterpolation.hessian u) y)≤U*dist x y^a := by
  sorry
end MomentQuotient

end

end OAI
end
