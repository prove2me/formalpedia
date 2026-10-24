-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_affineSubtract_potentialIntegrable_408915f
-- name    : FunctionalInequalities.Probability.MomentMeasure.affineSubtract_potentialIntegrable_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:30.894159+00:00
-- url     : https://prove2.me/theorems/319d7e4e-6926-407e-896f-18697bceb409
-- title:
--   Integrability Under Affine Subtraction
-- statement:
--   This states that affine subtraction preserves potential integrability under a first-moment hypothesis.
--
--   Let $\mu$ be a finite measure on a real inner-product space, let $f:E\to\overline{\mathbb R}$ be potential-integrable with respect to $\mu$, and let $a\in E$, $b\in\mathbb R$. Assume the identity map is integrable:
--
--   $$
--   \int\|x\|\,d\mu(x)<\infty.
--   $$
--
--   Then `affineSubtract f a b` is also potential-integrable with respect to $\mu$. No Borel-space instance is required by the statement, and no supporting affine plane is assumed.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Affine.lean#L67-L91 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Affine`, declaration `FunctionalInequalities.Probability.MomentMeasure.affineSubtract_potentialIntegrable`; the repository is private at upload time).

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

theorem FunctionalInequalities.Probability.MomentMeasure.affineSubtract_potentialIntegrable_408915f
    (f : E → EReal) (a : E) (b : ℝ) (hf : PotentialIntegrable f μ)
    (hfirst : Integrable (fun x : E => x) μ) :
    PotentialIntegrable (affineSubtract f a b) μ := by sorry
