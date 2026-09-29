-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_of_var_limit_of_bounded
-- name    : MarkovChainCLT.clt_of_var_limit_of_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-05T10:50:11.374467+00:00
-- url     : https://prove2.me/theorems/70424ff9-330e-40cc-9f5d-8390a8946cf5
-- title:
--   CLT for bounded sequences given variance convergence
-- statement:
--   Let $Y = (Y_n)_{n \ge 0}$ be a centered strictly stationary real-valued sequence on a probability space $(\Omega, \mathcal F, P)$, uniformly bounded ($|Y_n| < B$ almost surely for every $n$) with summable strong mixing coefficients $\sum_{n \ge 0}\alpha(n) < \infty$. Assume moreover that the normalized variances converge,
--   $$
--   \frac{1}{n} \mathrm{Var}(S_n) \to \sigma^2, \qquad S_n = \sum_{i=0}^{n-1} Y_i,
--   $$
--   where $\sigma^2 = E[Y_0^2] + 2\sum_{k \ge 1} E[Y_0 Y_k]$, and that $\sigma^2 > 0$. Then
--   $$
--   \frac{1}{\sqrt n} S_n \xrightarrow{d} N(0, \sigma^2).
--   $$
--   This is the blocking half of the Ibragimov--Linnik bounded-case central limit theorem (Jones, Theorem 5, condition 1): Bernstein big-block/small-block decomposition makes distant blocks asymptotically independent, so the normalized sum inherits the Gaussian limit from the independent-block approximation once the variance is known to stabilize. It takes the variance limit as a hypothesis, complementing the separately proved variance-convergence lemma.
--   **Formalization Note** Convergence is weak convergence of the laws under the common probability measure $P$; the Gaussian variance is the nonnegative-real coercion of $\sigma^2$, which equals $\sigma^2$ under the positivity hypothesis.
-- source:
--   G. L. Jones, On the Markov Chain Central Limit Theorem, Probability Surveys 1 (2004) 299-320, https://arxiv.org/abs/math/0409112, Theorem 5 condition 1; original result: I. A. Ibragimov and Yu. V. Linnik (1971), Ch. 18. Blocking step of the proof.

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- The blocking/limit component of the Ibragimov-Linnik bounded-case CLT, given variance convergence. -/

theorem MarkovChainCLT.clt_of_var_limit_of_bounded
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (B : ℝ) (hB : ∀ n, ∀ᵐ ω ∂P, |Y n ω| < B)
    (hα : Summable (fun n => alphaMixingCoef P Y n))
    (hvarlim : Tendsto (fun n : ℕ => Var[∑ i ∈ Finset.range n, Y i; P] / (n : ℝ))
      atTop (𝓝 (seqAsymptoticVariance P Y)))
    (hvar : 0 < seqAsymptoticVariance P Y) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
      atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal) := by sorry
