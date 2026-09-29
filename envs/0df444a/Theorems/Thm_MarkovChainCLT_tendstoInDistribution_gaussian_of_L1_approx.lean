-- Prove2me | Theorems.Thm_MarkovChainCLT_tendstoInDistribution_gaussian_of_L1_approx
-- name    : MarkovChainCLT.tendstoInDistribution_gaussian_of_L1_approx
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T01:15:50.096267+00:00
-- url     : https://prove2.me/theorems/5e6937e4-c4d6-4a8c-8558-4806197c087f
-- title:
--   A uniform L¹ approximation by Gaussian-convergent sequences forces a Gaussian limit
-- statement:
--   **The truncation closure of a central limit theorem.** Let $(Y_n)$ be a sequence of real random variables on a probability space, and suppose it is approximated, uniformly in $n$, by a family of auxiliary sequences $(W^K_n)_n$ indexed by $K$:
--   $$\sup_n \; \mathbb E\bigl|Y_n - W^K_n\bigr| \;\le\; \delta_K, \qquad \delta_K \to 0 .$$
--   Suppose moreover that each auxiliary sequence satisfies a central limit theorem, $W^K_n \Rightarrow N(0, v_K)$ as $n \to \infty$, and that the variances converge, $v_K \to v$. Then $Y_n \Rightarrow N(0, v)$.
--
--   **Discussion.** This is the standard "$3\varepsilon$" or *approximation* lemma that closes a truncation argument. Its content is that convergence in distribution, although not itself an $L^1$ notion, is stable under $L^1$ perturbations that are small **uniformly in $n$**. The uniformity is essential: without it one would have to diagonalise, choosing $K = K(n)$, and the conclusion could fail. Note also that the auxiliary variables $W^K_n$ need not be measurable in any strong sense — the almost-everywhere measurability contained in each hypothesis $W^K \Rightarrow N(0,v_K)$ is enough.
--
--   **Where this is used.** For the central limit theorem for a square-integrable observable $f$ of a uniformly ergodic Markov chain, one sets $f_K = $ the truncation of $f$ at level $K$, $Y_n = S_n(f)/\sqrt n$ and $W^K_n = S_n(f_K)/\sqrt n$. The bounded-observable theorem provides the CLT for each $W^K$; the $O(n)$ bound on the variance of partial sums gives $\mathbb E|Y_n - W^K_n| \le 2\sqrt N \, \|f - f_K\|_{L^2(\pi)}$, uniformly in $n$, which tends to $0$ by dominated convergence; and the Cauchy property of $(v_K)$, obtained from the characteristic function, supplies the limiting variance. This lemma then delivers the theorem.
--
--   **Proof.** Weak convergence on $\mathbb R$ is tested by bounded Lipschitz functions. Fix such an $f$, with Lipschitz constant $L$ and range of diameter at most $C$; the latter bounds $|f|$, so all the integrals below converge. Given $\varepsilon > 0$, choose $K$ so large that both $\bigl|\int f\,dN(0,v_K) - \int f\,dN(0,v)\bigr| < \varepsilon/3$ — possible because centred Gaussians depend weakly continuously on the variance — and $L\,\delta_K < \varepsilon/3$. For that fixed $K$, the hypothesis $W^K_n \Rightarrow N(0,v_K)$ gives $\bigl|\mathbb E f(W^K_n) - \int f\,dN(0,v_K)\bigr| < \varepsilon/3$ for all large $n$. Finally, for **every** $n$, the Lipschitz bound and monotonicity of the integral give $\bigl|\mathbb E f(Y_n) - \mathbb E f(W^K_n)\bigr| \le L\,\mathbb E|Y_n - W^K_n| \le L\,\delta_K < \varepsilon/3$. Adding the three estimates completes the proof.
-- source:
--   P. Billingsley, Convergence of Probability Measures, 2nd ed., Wiley 1999, Theorem 3.2 (the approximation theorem); G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320; I. A. Ibragimov and Yu. V. Linnik, Independent and Stationary Sequences of Random Variables, Wolters-Noordhoff 1971.

import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Portmanteau

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.tendstoInDistribution_gaussian_of_L1_approx {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (W : ℕ → ℕ → Ω → ℝ) (v : ℕ → ℝ≥0) (c : ℝ≥0) (δ : ℕ → ℝ)
    (hY : ∀ n, Measurable (Y n))
    (hW : ∀ K, TendstoInDistribution (W K) atTop (id : ℝ → ℝ) (fun _ => μ)
      (gaussianReal 0 (v K)))
    (hint : ∀ K n, Integrable (fun ω => |Y n ω - W K n ω|) μ)
    (hδ : ∀ K n, ∫ ω, |Y n ω - W K n ω| ∂μ ≤ δ K)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hv : Tendsto (fun K => (v K : ℝ)) atTop (𝓝 (c : ℝ))) :
    TendstoInDistribution Y atTop (id : ℝ → ℝ) (fun _ => μ) (gaussianReal 0 c) := by sorry
