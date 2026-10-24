-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_covariance_quadraticTilt_tendsto_408915f
-- name    : FunctionalInequalities.Probability.covariance_quadraticTilt_tendsto_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:20:29.185482+00:00
-- url     : https://prove2.me/theorems/9a7da0ca-234b-4ef0-9b43-8478d9757905
-- title:
--   Operator Covariance Convergence Under Tilting
-- statement:
--   This formalizes covariance convergence for the small quadratic tilts used in the regular approximation, associated in the literature register with Section 2, equation (12), of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $E$ be a complete finite-dimensional real inner-product space with Borel measurable structure, let $\mu$ be a probability measure, and assume the identity map has finite second moment: `MemLp id 2 μ`. Let
--   $\mu_\delta=\mu.\operatorname{tilted}(x\mapsto-\delta\|x\|^2/2)$.
--
--   Then, as $\delta\to0^+$,
--
--   $$
--   \operatorname{Cov}(\mu_\delta)\longrightarrow\operatorname{Cov}(\mu)
--   $$
--
--   in the topology of continuous linear operators, hence in operator norm. This is a convergence statement only; it does not assert log-concavity or invertibility of either covariance operator.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Section 2, (12), p. 5 (unnumbered). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/QuadraticTilt.lean#L216-L245 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.QuadraticTilt`, declaration `FunctionalInequalities.Probability.covariance_quadraticTilt_tendsto`; the repository is private at upload time).

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

theorem FunctionalInequalities.Probability.covariance_quadraticTilt_tendsto_408915f (μ : ProbabilityMeasure E)
    (hμ2 : MemLp (id : E → E) 2 (μ : Measure E)) :
    Tendsto (fun δ : ℝ => Covariance.operator
      ((μ : Measure E).tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (Covariance.operator (μ : Measure E))) := by sorry
