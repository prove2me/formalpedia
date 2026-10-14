-- Prove2me | Theorems.Thm_GIGnBounds_Tail_theorem_2
-- name    : GIGnBounds.Tail.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:19.839809+00:00
-- url     : https://prove2.me/theorems/80e3003c-60a6-469b-981e-97512bacef70
-- title:
--   Theorem 2 — for $r^*>2.5$, explicit bounds on $P(L(\infty)\ge x/(1-\rho))$ and on the probability of delay in the GI/GI/n queue
-- statement:
--   Consider the FCFS GI/GI/$n$ queue ($n\ge1$) whose inter-arrival times have the law of a random variable $A$ and whose service times have the law of $S$, both nonnegative with finite positive means. Write $\mu_A=1/\mathbb E[A]$, $\mu_S=1/\mathbb E[S]$, $\rho=\mu_A/(n\mu_S)$, and $r^*=\sup\{r:\mathbb E[S^r]<\infty\}$ (possibly $\infty$). Suppose
--
--   1. $\mathbb E[A^2]<\infty$;
--   2. $r^*>2.5$;
--   3. $\mu_A<n\mu_S$;
--   4. $Q(\infty)$ exists: from every initial condition the number in system converges in distribution to $Q(\infty)$; and $L(\infty)=\max(0,Q(\infty)-n)$.
--
--   **Theorem 2.** For all $x>0$, $\mathbb P\big(L(\infty)\ge\frac x{1-\rho}\big)$ is at most
--
--   $$\inf_{r\in[2.5,r^*)}\Big(2\times10^4\,\mathbb E[(S\mu_S)^2]\,(10^6)^r\Big(\big(\mathbb E[(S\mu_S)^2]\big)^{r-1}r^{2.5r}+r^{1.5r}\,\mathbb E[(S\mu_S)^r]\Big)x^{-\frac r2}\Big)+1.1\exp\Big(-.0225\big(\mathbb E[(A\mu_A)^2]\big)^{-1}x\Big);$$
--
--   and the steady-state probability of delay $\mathbb P(Q(\infty)\ge n)$ is at most
--
--   $$\inf_{r\in[2.5,r^*)}\Big(2\times10^4\,\mathbb E[(S\mu_S)^2]\,(10^7)^r\Big(\big(\mathbb E[(S\mu_S)^2]\big)^{r-1}r^{2.5r}+r^{1.5r}\,\mathbb E[(S\mu_S)^r]\Big)\big(n(1-\rho)^2\big)^{-\frac r2}\Big)+1.1\exp\Big(-.0028\big(\mathbb E[(A\mu_A)^2]\big)^{-1}n(1-\rho)^2\Big).$$
--
--   These are explicit, $n$-free bounds that scale like $1/(1-\rho)$, as Kingman's bound does for one server, and they hold in every traffic regime, including the Halfin–Whitt regime.
--
--   **Formalization Note.** "$\le\inf_r f(r)+g$" with $g$ independent of $r$ and a nonempty range is stated as "$\le f(r)+g$ for every $r\in[2.5,r^*)$". The decimal constants are exact rationals ($2\cdot10^4$, $225/10000$, $28/10000$, $11/10$, $5/2$, $3/2$). $0<\mathbb E[A]$ and $0<\mathbb E[S]$ are implicit in the paper (μ must be finite). "$Q(\infty)$ exists" quantifies over initial laws without jobs waiting at time $0$ (first-arrival time and residual service times only); this is a weaker hypothesis than the paper's, so the theorem stated is stronger, and the paper's proof (Lemma 7 via Lemma 14) only uses such initial conditions. $\mathbb E[(S\mu_S)^r]$ is finite because $r<r^*$.
-- source:
--   Li and Goldberg, Simple and explicit bounds for multi-server queues with 1/(1−ρ) scaling, arXiv:1706.04628v3, pp. 9–10, Theorem 2

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory

namespace GIGnBounds.Tail

/-- **Theorem 2** (Li–Goldberg, arXiv:1706.04628v3, pp. 9–10). For the FCFS GI/GI/n queue with
`E[A²] < ∞`, `r* > 2.5`, `μ_A < n μ_S` and `Q(∞)` existing (law `π`), for every `x > 0` and every
`r ∈ [2.5, r*)` the tail `P(L(∞) ≥ x/(1−ρ))` of the number waiting, and the steady-state probability of
delay `P(Q(∞) ≥ n)`, obey the explicit bounds below. (The paper's `inf_r` is stated as `∀ r`.) -/
theorem theorem_2 (n : ℕ) (hn : 0 < n) (μA μS : Measure ℝ) [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    (hA : IsTimeLaw μA) (hS : IsTimeLaw μS)
    (hA2 : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂μA < ⊤)
    (hr : (((5 : ℝ) / 2 : ℝ) : EReal) < rStar μS)
    (hstab : rate μA < n * rate μS)
    (π : Measure ℕ) (hπ : IsSteadyStateLaw n μA μS π) :
    (∀ x : ℝ, 0 < x → ∀ r : ℝ, (5 : ℝ) / 2 ≤ r → (r : EReal) < rStar μS →
      π.real {q : ℕ | x / (1 - rho n μA μS) ≤ ((q - n : ℕ) : ℝ)} ≤
        2 * 10 ^ 4 * nMoment μS 2 * ((10 : ℝ) ^ 6) ^ r *
            (nMoment μS 2 ^ (r - 1) * r ^ ((5 : ℝ) / 2 * r) + r ^ ((3 : ℝ) / 2 * r) * nMoment μS r) *
            x ^ (-(r / 2)) +
          11 / 10 * Real.exp (-((225 : ℝ) / 10000) * (nMoment μA 2)⁻¹ * x)) ∧
    (∀ r : ℝ, (5 : ℝ) / 2 ≤ r → (r : EReal) < rStar μS →
      π.real {q : ℕ | n ≤ q} ≤
        2 * 10 ^ 4 * nMoment μS 2 * ((10 : ℝ) ^ 7) ^ r *
            (nMoment μS 2 ^ (r - 1) * r ^ ((5 : ℝ) / 2 * r) + r ^ ((3 : ℝ) / 2 * r) * nMoment μS r) *
            ((n : ℝ) * (1 - rho n μA μS) ^ 2) ^ (-(r / 2)) +
          11 / 10 * Real.exp (-((28 : ℝ) / 10000) * (nMoment μA 2)⁻¹ * n * (1 - rho n μA μS) ^ 2)) := by sorry

end GIGnBounds.Tail
