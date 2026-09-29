-- Prove2me | Theorems.Thm_MeasureTheory_tendsto_integral_of_tendstoInMeasure_of_bounded
-- name    : MeasureTheory.tendsto_integral_of_tendstoInMeasure_of_bounded
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T22:25:25.891216+00:00
-- url     : https://prove2.me/theorems/f238630a-f660-410e-a487-8539feb5fe03
-- title:
--   Bounded convergence theorem for convergence in probability
-- statement:
--   **Bounded convergence theorem, with convergence in probability in place of almost-everywhere convergence.** If $(G_n)$ is a uniformly bounded sequence of real random variables, $|G_n| \le B$ everywhere, and $G_n \to 0$ in probability, then
--   $$\mathbb E[G_n] \;\longrightarrow\; 0 .$$
--
--   **Why the usual dominated convergence theorem does not apply.** Convergence in probability does not imply almost-everywhere convergence — the classical "typewriter" sequence of indicators of sliding intervals on $[0,1]$ converges in probability to $0$ while converging almost nowhere. One can always extract an a.e.-convergent *subsequence*, but recovering the full limit from that requires a sub-subsequence argument. The direct proof below avoids it entirely.
--
--   **Proof.** Fix $\delta>0$ and split the space according to the size of $G_n$:
--   $$|G_n| \;\le\; \delta \;+\; B\,\mathbf 1_{\{|G_n|\ge\delta\}} \qquad\text{pointwise,}$$
--   because on $\{|G_n|<\delta\}$ the first term already dominates, and on $\{|G_n|\ge\delta\}$ the second does. Integrating against the probability measure,
--   $$\bigl|\mathbb E[G_n]\bigr| \;\le\; \mathbb E|G_n| \;\le\; \delta + B\,\mathbb P\bigl(|G_n|\ge\delta\bigr).$$
--   Convergence in probability makes the second term vanish as $n\to\infty$ for each fixed $\delta$, so $\limsup_n |\mathbb E[G_n]| \le \delta$; since $\delta>0$ was arbitrary, the limit is $0$. Taking $\delta = \varepsilon/2$ and then $n$ large enough that $B\,\mathbb P(|G_n|\ge\varepsilon/2) < \varepsilon/2$ turns this into the explicit $\varepsilon$–$N$ statement.
--
--   **Where it is used.** This is the standard device for discarding asymptotically negligible remainders inside expectations of *bounded* test functions. In central limit theorems for dependent sequences one compares $\mathbb E[F(S_n)]$ with $\mathbb E[F(S_n')]$ where $S_n - S_n' \to 0$ in probability and $F$ is bounded and Lipschitz; then $G_n = F(S_n) - F(S_n')$ is bounded by $2\|F\|_\infty$ and tends to $0$ in probability, and this lemma yields $\mathbb E[F(S_n)] - \mathbb E[F(S_n')] \to 0$. No integrability of $S_n$ itself is needed anywhere.
-- source:
--   P. Billingsley, Convergence of Probability Measures, 2nd ed., Wiley 1999, Section 3; P. Billingsley, Probability and Measure, 3rd ed., Wiley 1995, Theorem 25.12 and Section 5.

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem MeasureTheory.tendsto_integral_of_tendstoInMeasure_of_bounded {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (G : ℕ → Ω → ℝ)
    (hG : ∀ n, Measurable (G n)) (B : ℝ) (hB : ∀ n ω, |G n ω| ≤ B)
    (h0 : TendstoInMeasure μ G atTop 0) :
    Tendsto (fun n => ∫ ω, G n ω ∂μ) atTop (𝓝 0) := by sorry
