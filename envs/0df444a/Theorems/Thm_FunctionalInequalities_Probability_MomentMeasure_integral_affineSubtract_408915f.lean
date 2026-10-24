-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_integral_affineSubtract_408915f
-- name    : FunctionalInequalities.Probability.MomentMeasure.integral_affineSubtract_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:28.519344+00:00
-- url     : https://prove2.me/theorems/314068fc-a68b-4cce-a029-749f394d587c
-- title:
--   Integral Formula for Affine Subtraction
-- statement:
--   This gives the exact integral correction under affine subtraction.
--
--   Let $\mu$ be a finite measure, let $f:E\to\overline{\mathbb R}$ be potential-integrable, let $a\in E$, and let $b\in\mathbb R$. Assume the identity map is integrable with respect to $\mu$. Then
--
--   $$
--   \int \operatorname{toReal}\bigl((\operatorname{affineSubtract} f\ a\ b)(x)\bigr)\,d\mu
--   =
--   \int \operatorname{toReal}(f(x))\,d\mu
--   -\int\langle a,x\rangle\,d\mu
--   -(\mu(E)).\operatorname{toReal}\,b.
--   $$
--
--   The total mass factor is retained; invariance under constant shifts is therefore not asserted for arbitrary finite measures.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Affine.lean#L92-L112 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Affine`, declaration `FunctionalInequalities.Probability.MomentMeasure.integral_affineSubtract`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Analysis
section
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
section StructuredSpace
variable [IsFiniteMeasure μ]
omit [BorelSpace E]

theorem FunctionalInequalities.Probability.MomentMeasure.integral_affineSubtract_408915f
    (f : E → EReal) (a : E) (b : ℝ) (hf : PotentialIntegrable f μ)
    (hfirst : Integrable (fun x : E => x) μ) :
    (∫ x, (affineSubtract f a b x).toReal ∂μ) =
      (∫ x, (f x).toReal ∂μ) - (∫ x, inner ℝ a x ∂μ) - (μ Set.univ).toReal * b := by sorry
