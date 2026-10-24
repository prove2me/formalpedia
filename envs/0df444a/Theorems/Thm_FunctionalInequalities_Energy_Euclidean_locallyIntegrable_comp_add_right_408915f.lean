-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_Euclidean_locallyIntegrable_comp_add_right_408915f
-- name    : FunctionalInequalities.Energy.Euclidean.locallyIntegrable_comp_add_right_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:57.488557+00:00
-- url     : https://prove2.me/theorems/47355370-8900-4f93-91db-43b591c71ead
-- title:
--   Local Integrability Under Haar Translation
-- statement:
--   This states stability of local integrability under translation.
--
--   Let $V$ be a finite-dimensional real inner-product space with its Borel measurable structure, let $m$ be an additive Haar measure on $V$, and let $h:V\to\mathbb R$ be locally integrable with respect to $m$. For every $v\in V$, the translated function
--
--   $$
--    x\longmapsto h(x+v)
--   $$
--
--   is also locally integrable with respect to $m$.
--
--   This is a measure-theoretic auxiliary fact used when comparing a function with its translates in weak-gradient arguments.
--
--   **Formalization Note** The declaration omits the second-countable-topology assumption; the additive Haar-measure instance is explicit.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/ZeroGradient.lean#L250-L266 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.ZeroGradient`, declaration `FunctionalInequalities.Energy.Euclidean.locallyIntegrable_comp_add_right`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.Euclidean
end FunctionalInequalities.Energy.Euclidean
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (m : Measure V) [m.IsAddHaarMeasure]
omit [SecondCountableTopology V]

theorem FunctionalInequalities.Energy.Euclidean.locallyIntegrable_comp_add_right_408915f {h : V → ℝ} (hh : LocallyIntegrable h m) (v : V) :
    LocallyIntegrable (fun x => h (x + v)) m := by sorry
