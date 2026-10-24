-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_integral_quadraticTilt_tendsto_408915f
-- name    : FunctionalInequalities.Probability.integral_quadraticTilt_tendsto_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:20:32.699331+00:00
-- url     : https://prove2.me/theorems/10116887-fedc-4da5-be76-33a551a1e298
-- title:
--   Convergence of Small Quadratic Tilts
-- statement:
--   This formalizes the normalized small-quadratic-tilt convergence described in the source module for the regular approximation of Bizeul–Klartag–Lehec (arXiv:2610.05474v1, Section 2, p. 5).
--
--   Let $E$ be a Borel real normed space, let $F$ be a complete real normed space, let $\mu$ be a probability measure on $E$, let $f:E\to F$ be integrable with respect to $\mu$, and for $\delta\in\mathbb R$ define the tilted measure by the weight $e^{-\delta\|x\|^2/2}$. As $\delta\to0^+$,
--
--   $$
--   \int f(x)\,d\bigl(\mu.\operatorname{tilted}(x\mapsto-\tfrac\delta2\|x\|^2)\bigr)(x)
--   \longrightarrow \int f(x)\,d\mu(x).
--   $$
--
--   The limit is in the norm topology of $F$ and is taken through positive $\delta$. Only probability and integrability are assumed; no moment or log-concavity hypothesis is added.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/QuadraticTilt.lean#L26-L90 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.QuadraticTilt`, declaration `FunctionalInequalities.Probability.integral_quadraticTilt_tendsto`; the repository is private at upload time).

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

theorem FunctionalInequalities.Probability.integral_quadraticTilt_tendsto_408915f {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) [IsProbabilityMeasure μ] (f : E → F) (hf : Integrable f μ) :
    Tendsto
      (fun δ : ℝ => ∫ x, f x ∂(μ.tilted (fun x => -(δ / 2) * ‖x‖ ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, f x ∂μ)) := by sorry
