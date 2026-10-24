-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_density_scaled_le_exp_408915f
-- name    : FunctionalInequalities.Probability.MomentMeasure.density_scaled_le_exp_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:21:35.419747+00:00
-- url     : https://prove2.me/theorems/da5dea2c-20af-4078-91b5-36c2ef958ea2
-- title:
--   Scaled Legendre Density Exponential Bound
-- statement:
--   This is a technical density estimate for a nonnegative extended-real Legendre transform.
--
--   Let $E$ be a real inner-product normed additive group, let $\phi:E\to\overline{\mathbb R}$, and let $c,C,M,a\in\mathbb R$. Assume:
--
--   1. $0\le C$.
--   2. $1\le a$ and $M\le a$.
--   3. For every $y\in E$, the Legendre transform $\phi^*(y)$ is nonnegative and satisfies
--      $$c\|y\|-CM\le \phi^*(y).$$
--
--   Then, for every $y\in E$, the density associated with `density` and the scaled point $ay$ obeys
--   $$\operatorname{density}(\phi^*)(ay)\le \operatorname{ENNReal.ofReal}\!\left(\exp(C-c\|y\|)\right).$$
--
--   This provides a reusable exponential envelope after scaling, without finite-dimensionality or measurability assumptions in the statement.
--
--   **Formalization Note** The density and bound are $[0,\infty]$-valued (`ENNReal`); the exponent is an ordinary real number.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean#L100-L119 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Coercivity`, declaration `FunctionalInequalities.Probability.MomentMeasure.density_scaled_le_exp`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LiminfLimsup
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
open MeasureTheory Filter Set
open scoped ENNReal Topology
section Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.MomentMeasure.density_scaled_le_exp_408915f (φ : E → EReal) {c C M a : ℝ}
    (hC : 0 ≤ C) (ha : 1 ≤ a) (hMa : M ≤ a)
    (hlower : ∀ y, 0 ≤ legendre φ y ∧ ((c * ‖y‖ - C * M : ℝ) : EReal) ≤ legendre φ y)
    (y : E) : density (legendre φ) (a • y) ≤ ENNReal.ofReal (Real.exp (C - c * ‖y‖)) := by sorry
