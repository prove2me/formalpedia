-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_inner_covariance_quadraticTilt_tendsto_408915f
-- name    : FunctionalInequalities.Probability.inner_covariance_quadraticTilt_tendsto_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:20:22.404836+00:00
-- url     : https://prove2.me/theorems/b492bfd0-7007-4ff7-b99b-546fec96df7d
-- title:
--   Pointwise Covariance Convergence Under Tilting
-- statement:
--   This is the scalar covariance convergence statement for small quadratic tilts.
--
--   Let $E$ be a complete finite-dimensional real inner-product space with Borel measurable structure, let $\mu$ be a probability measure with finite second moment, expressed as `MemLp id 2 μ`, and let $u,v\in E$. For the tilted probability measure with weight $e^{-\delta\|x\|^2/2}$,
--
--   $$
--   \left\langle \operatorname{Cov}(\mu_\delta)u,v\right\rangle
--   \longrightarrow
--   \left\langle \operatorname{Cov}(\mu)u,v\right\rangle
--   \qquad(\delta\to0^+).
--   $$
--
--   The convergence is in $\mathbb R$ along the one-sided neighborhood of zero. This scalar form is the ingredient used to establish operator-norm covariance convergence.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/QuadraticTilt.lean#L187-L214 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.QuadraticTilt`, declaration `FunctionalInequalities.Probability.inner_covariance_quadraticTilt_tendsto`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_QuadraticTilt
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section
open MeasureTheory Filter Topology Set
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section Covariance
open ProbabilityTheory
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.inner_covariance_quadraticTilt_tendsto_408915f (μ : ProbabilityMeasure E)
    (hμ2 : MemLp (id : E → E) 2 (μ : Measure E)) (u v : E) :
    Tendsto (fun δ : ℝ => ⟪Covariance.operator
      ((μ : Measure E).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)) u, v⟫)
      (𝓝[>] (0 : ℝ)) (𝓝 ⟪Covariance.operator (μ : Measure E) u, v⟫) := by sorry
