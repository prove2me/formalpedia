-- Prove2me | Theorems.Thm_GIGnBounds_Tail_theorem_10
-- name    : GIGnBounds.Tail.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:03.430129+00:00
-- url     : https://prove2.me/theorems/72f0dfc3-4f2e-428e-94e0-be095556e052
-- title:
--   Theorem 10 — central-moment bounds imply an explicit bound on (4) for $x\ge18$
-- statement:
--   Let $\mathbb E[S]=1$, $n\ge1$, $C_1,C_2>0$, $r_1>s>1$, $r_2>2$. Here $\{\mathcal N_{e,i},1\le i\le n\}$ are independent equilibrium renewal processes with renewals distributed as $S$, and $N_{e,i}(t)$ their numbers of renewals in $[0,t]$. $\mathcal A_e$ is an independent equilibrium renewal process with renewals distributed as $A$, $A_e(t)$ its count, and $\mathbb E[A^2]<\infty$. Assume
--   1. $\mu_A<n$;
--   2. for all $t\ge1$, $\mathbb E\big[|\sum_{i=1}^nN_{e,i}(t)-nt|^{r_1}\big]\le C_1n^{r_1/2}t^s$;
--   3. for all $t\in[2/n,1]$, $\mathbb E\big[|\sum_{i=1}^nN_{e,i}(t)-nt|^{r_2}\big]\le C_2(nt)^{r_2/2}$.
--
--   **Theorem 10.** For all $x\ge18$, $\mathbb P\big(\sup_{t\ge0}(A_e(t)-\sum_{i=1}^nN_{e,i}(t))\ge x\big)$ is at most
--
--   $$1.8\Big(1+\frac1{r_1-s}\Big)\Big(32\frac{r_1+1}{s-1}\Big)^{r_1+1}C_1n^{\frac{r_1}2}(n-\mu_A)^{-s}x^{-(r_1-s)}+1.8\Big(1+\frac1{r_1-s}\Big)\Big(46\frac{r_2+1}{\frac{r_2}2-1}\Big)^{r_2+1}C_2n^{\frac{r_2}2}(n-\mu_A)^{-\frac{r_2}2}x^{-\frac{r_2}2}+1.1\exp\Big(-.045\frac{n-\mu_A}{n+\mu_A}\big(\mathbb E[(A\mu_A)^2]\big)^{-1}x\Big).$$
--
--   This is the conditional bound for (4) that the main proof instantiates with Lemmas 5 and 6.
--
--   **Formalization Note.** The page does not list $\mathbb E[A^2]<\infty$, but the last term is meaningless without it (Lemma 3 is applied in the proof); it is a disclosed added hypothesis. Without it Lean's value of $\mathbb E[(A\mu_A)^2]$ would be $0$ and the last term would collapse to $1.1$. The moment hypotheses are lower Lebesgue integrals, as in Lemma 4.
-- source:
--   Li and Goldberg, Simple and explicit bounds for multi-server queues with 1/(1−ρ) scaling, arXiv:1706.04628v3, p. 26, Theorem 10

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory

namespace GIGnBounds.Tail

/-- **Theorem 10** (Li–Goldberg, arXiv:1706.04628v3, p. 26). Let `E[S] = 1`, `n ≥ 1`, `C₁, C₂ > 0`,
`r₁ > s > 1`, `r₂ > 2`, with (i) `μ_A < n`, and the central-moment bounds (ii) for `t ≥ 1` and (iii)
for `t ∈ [2/n, 1]`. Then for all `x ≥ 18` the supremum (4) obeys the explicit bound below.
`E[A²] < ∞` is required for the last term (Lemma 3 is applied). -/
theorem theorem_10 (n : ℕ) (hn : 1 ≤ n) (μA μS : Measure ℝ) [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    (hA : IsTimeLaw μA) (hS : IsTimeLaw μS)
    (hS1 : mean μS = 1) (hA2 : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂μA < ⊤)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : RenewalFamily Ω P n μA μS) (C₁ C₂ r₁ r₂ s : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hr₁s : s < r₁) (hs : 1 < s) (hr₂ : 2 < r₂)
    (hi : rate μA < n)
    (hii : ∀ t : ℝ, 1 ≤ t →
      ∫⁻ ω, ENNReal.ofReal (|∑ i, (F.Ne i ω t : ℝ) - n * t| ^ r₁) ∂P ≤ ENNReal.ofReal (C₁ * (n : ℝ) ^ (r₁ / 2) * t ^ s))
    (hiii : ∀ t : ℝ, 2 / (n : ℝ) ≤ t → t ≤ 1 →
      ∫⁻ ω, ENNReal.ofReal (|∑ i, (F.Ne i ω t : ℝ) - n * t| ^ r₂) ∂P ≤ ENNReal.ofReal (C₂ * ((n : ℝ) * t) ^ (r₂ / 2)))
    (x : ℝ) (hx : 18 ≤ x) :
    P.real {ω | (x : EReal) ≤ supFrom (fun t => (F.Ae ω t : ℝ) - ∑ i, (F.Ne i ω t : ℝ))} ≤
      18 / 10 * (1 + 1 / (r₁ - s)) * (32 * (r₁ + 1) / (s - 1)) ^ (r₁ + 1) * C₁ *
          (n : ℝ) ^ (r₁ / 2) * (n - rate μA) ^ (-s) * x ^ (-(r₁ - s)) +
        18 / 10 * (1 + 1 / (r₁ - s)) * (46 * (r₂ + 1) / (r₂ / 2 - 1)) ^ (r₂ + 1) * C₂ *
          (n : ℝ) ^ (r₂ / 2) * (n - rate μA) ^ (-(r₂ / 2)) * x ^ (-(r₂ / 2)) +
        11 / 10 * Real.exp (-((45 : ℝ) / 1000) * ((n - rate μA) / (n + rate μA)) *
          (nMoment μA 2)⁻¹ * x) := by sorry

end GIGnBounds.Tail
