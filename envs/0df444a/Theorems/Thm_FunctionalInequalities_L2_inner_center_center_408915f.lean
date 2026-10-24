-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_inner_center_center_408915f
-- name    : FunctionalInequalities.L2.inner_center_center_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:33:49.631354+00:00
-- url     : https://prove2.me/theorems/3b5cc94d-e98c-42c0-8faf-e661a710480c
-- title:
--   Inner Product of Centered $L^2$ Functions
-- statement:
--   This statement gives the inner-product identity for centered functions on a probability space.
--
--   Let $\mu$ be a probability measure on a measurable space and let $f,g\in L^2(\mu)$. With `center` defined by subtracting the respective means,
--
--   $$\left\langle f-\int f\,d\mu,\,g-\int g\,d\mu\right\rangle_{L^2(\mu)}
--   =\langle f,g\rangle_{L^2(\mu)}-\left(\int f\,d\mu\right)\left(\int g\,d\mu\right).$$
--
--   This elementary identity is reusable for variance, orthogonality, and centered-gradient calculations.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/MeanVariance.lean#L187-L203 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.MeanVariance`, declaration `FunctionalInequalities.L2.inner_center_center`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
variable {α : Type*} [MeasurableSpace α]

theorem FunctionalInequalities.L2.inner_center_center_408915f (μ : ProbabilityMeasure α)
    (f g : Lp ℝ 2 (μ : Measure α)) :
    inner ℝ (center μ f) (center μ g) =
      inner ℝ f g - mean μ f * mean μ g := by sorry
