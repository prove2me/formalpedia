-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_exists_uniform_norm_moments_tilted_quadraticExponent_of_compact_408915f
-- name    : FunctionalInequalities.Probability.Posterior.exists_uniform_norm_moments_tilted_quadraticExponent_of_compact_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:29:53.911362+00:00
-- url     : https://prove2.me/theorems/98b65d33-0f7a-4556-b27d-865a71882dcd
-- title:
--   Uniform Posterior Bounds for All Norm Moments
-- statement:
--   This statement formalizes a uniform moment bound in the compact-prior stage associated with Equation (67), p. 19, of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $E$ be a finite-dimensional real inner-product space and let $\mu$ be a probability measure with compact support. Then there exists a radius $R\in\mathbb R$ such that $0\leq R$ and, for every $c\in E$, every continuous linear map $Q:E\to E$, and every $p\in\mathbb N$, the posterior associated with `quadraticExponent c Q` satisfies
--
--   1. $x\mapsto\|x\|^p$ is integrable under the tilted measure;
--   2. its moment is bounded by $R^p$:
--
--   $$
--   \int_E \|x\|^p\,d\mu_{c,Q}(x)\leq R^p.
--   $$
--
--   The same support radius works uniformly for all finite parameters $(c,Q)$ and all natural exponents $p$. The conclusion is an existence statement for $R$, not a claim that a particular displayed radius is chosen.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/CompactQuadratic.lean#L58-L84 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.CompactQuadratic`, declaration `FunctionalInequalities.Probability.Posterior.exists_uniform_norm_moments_tilted_quadraticExponent_of_compact`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Covariance

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Posterior
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem FunctionalInequalities.Probability.Posterior.exists_uniform_norm_moments_tilted_quadraticExponent_of_compact_408915f (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (c : E) (Q : E →L[ℝ] E) (p : ℕ),
      Integrable (fun x => ‖x‖ ^ p) ((μ : Measure E).tilted (quadraticExponent c Q)) ∧
      (∫ x, ‖x‖ ^ p ∂((μ : Measure E).tilted (quadraticExponent c Q))) ≤ R ^ p := by sorry
