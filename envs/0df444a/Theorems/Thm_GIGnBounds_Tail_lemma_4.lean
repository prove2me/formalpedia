-- Prove2me | Theorems.Thm_GIGnBounds_Tail_lemma_4
-- name    : GIGnBounds.Tail.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:02.326921+00:00
-- url     : https://prove2.me/theorems/f4032adc-07b5-4ddb-b519-812f89055a66
-- title:
--   Lemma 4 — central-moment bounds on $\sum_i N_{e,i}(t)-nt$ imply a bound on the service supremum (6)
-- statement:
--   Let $\mathbb E[S]=1$, $n\ge1$, $C_1,C_2>0$, $r_1>s>1$, $r_2>2$. Here $\{\mathcal N_{e,i},1\le i\le n\}$ are independent equilibrium renewal processes with renewals distributed as $S$, and $N_{e,i}(t)$ their numbers of renewals in $[0,t]$. Assume
--   1. for all $t\ge1$, $\mathbb E\big[|\sum_{i=1}^nN_{e,i}(t)-nt|^{r_1}\big]\le C_1n^{r_1/2}t^s$;
--   2. for all $t\in[2/n,1]$, $\mathbb E\big[|\sum_{i=1}^nN_{e,i}(t)-nt|^{r_2}\big]\le C_2(nt)^{r_2/2}$.
--
--   **Lemma 4.** For all $\nu>0$ and $x\ge8$,
--
--   $$\mathbb P\Big(\sup_{t\ge0}\Big(nt-\sum_{i=1}^nN_{e,i}(t)-\nu t\Big)\ge x\Big)\le3.6\Big(1+\frac1{r_1-s}\Big)\Big(\Big(16\frac{r_1+1}{s-1}\Big)^{r_1+1}C_1n^{\frac{r_1}2}\nu^{-s}x^{-(r_1-s)}+\Big(23\frac{r_2+1}{\frac{r_2}2-1}\Big)^{r_2+1}C_2n^{\frac{r_2}2}(x\nu)^{-\frac{r_2}2}\Big).$$
--
--   It turns moment control of the pooled renewal process into a tail bound for its supremum with linear drift.
--
--   **Formalization Note.** The expectations of the nonnegative quantities in (i)–(ii) are lower Lebesgue integrals in $[0,\infty]$, so the hypotheses include their finiteness and need no integrability side condition. Powers with real exponents are `rpow`; $3.6$ is $36/10$.
-- source:
--   Li and Goldberg, Simple and explicit bounds for multi-server queues with 1/(1−ρ) scaling, arXiv:1706.04628v3, pp. 25–26, Lemma 4

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory

namespace GIGnBounds.Tail

/-- **Lemma 4** (Li–Goldberg, arXiv:1706.04628v3, pp. 25–26). Let `E[S] = 1`, `n ≥ 1`, `C₁, C₂ > 0`,
`r₁ > s > 1`, `r₂ > 2`, and suppose the pooled equilibrium renewal process satisfies the central-moment
bounds (i) for `t ≥ 1` and (ii) for `t ∈ [2/n, 1]`. Then for all `ν > 0` and `x ≥ 8` the service
supremum obeys the explicit bound below. -/
theorem lemma_4 (n : ℕ) (hn : 1 ≤ n) (μS : Measure ℝ) [IsProbabilityMeasure μS]
    (hS : IsTimeLaw μS) (hS1 : mean μS = 1)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ServiceFamily Ω P n μS) (C₁ C₂ r₁ r₂ s : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hr₁s : s < r₁) (hs : 1 < s) (hr₂ : 2 < r₂)
    (hi : ∀ t : ℝ, 1 ≤ t →
      ∫⁻ ω, ENNReal.ofReal (|∑ i, (F.Ne i ω t : ℝ) - n * t| ^ r₁) ∂P ≤ ENNReal.ofReal (C₁ * (n : ℝ) ^ (r₁ / 2) * t ^ s))
    (hii : ∀ t : ℝ, 2 / (n : ℝ) ≤ t → t ≤ 1 →
      ∫⁻ ω, ENNReal.ofReal (|∑ i, (F.Ne i ω t : ℝ) - n * t| ^ r₂) ∂P ≤ ENNReal.ofReal (C₂ * ((n : ℝ) * t) ^ (r₂ / 2)))
    (ν x : ℝ) (hν : 0 < ν) (hx : 8 ≤ x) :
    P.real {ω | (x : EReal) ≤ supFrom (fun t => n * t - ∑ i, (F.Ne i ω t : ℝ) - ν * t)} ≤
      36 / 10 * (1 + 1 / (r₁ - s)) *
        ((16 * (r₁ + 1) / (s - 1)) ^ (r₁ + 1) * C₁ * (n : ℝ) ^ (r₁ / 2) * ν ^ (-s) * x ^ (-(r₁ - s)) +
          (23 * (r₂ + 1) / (r₂ / 2 - 1)) ^ (r₂ + 1) * C₂ * (n : ℝ) ^ (r₂ / 2) *
            (x * ν) ^ (-(r₂ / 2))) := by sorry

end GIGnBounds.Tail
