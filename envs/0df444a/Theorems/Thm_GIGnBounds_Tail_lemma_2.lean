-- Prove2me | Theorems.Thm_GIGnBounds_Tail_lemma_2
-- name    : GIGnBounds.Tail.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:49.216987+00:00
-- url     : https://prove2.me/theorems/e8e2ff51-c8ce-4b72-8072-51940e1d792c
-- title:
--   Lemma 2 — union bound splitting (4) into the arrival supremum (5) and the service supremum (6)
-- statement:
--   Let $\mathbb E[S]=1$ and $\mu_A<n$. Here $(\Omega,\mathcal F,\mathbb P)$ is any probability space carrying a **bounding family**: an equilibrium renewal process $\mathcal A_e$ with renewals distributed as $A$ (first interval distributed as $R(A)$), and $n$ equilibrium renewal processes $\mathcal N_{e,1},\dots,\mathcal N_{e,n}$ with renewals distributed as $S$ (first interval $R(S)$), all intervals of all processes mutually independent. $A_e(t)$ and $N_{e,i}(t)$ are their numbers of renewals in $[0,t]$. $A_o(t)$ is the ordinary renewal process formed by the renewals of $\mathcal A_e$ after the first one (so $A_e(t)\le1+A_o(t)$).
--
--   **Lemma 2.** For every $x>2$,
--
--   $$\mathbb P\Big(\sup_{t\ge0}\Big(A_e(t)-\sum_{i=1}^n N_{e,i}(t)\Big)\ge x\Big)\le \mathbb P\Big(\sup_{t\ge0}\Big(A_o(t)-\mu_At-\tfrac12(n-\mu_A)t\Big)\ge\tfrac12x-1\Big)+\mathbb P\Big(\sup_{t\ge0}\Big(nt-\sum_{i=1}^n N_{e,i}(t)-\tfrac12(n-\mu_A)t\Big)\ge\tfrac12x\Big).$$
--
--   It separates the arrival fluctuations from the pooled service fluctuations, each with half of the drift $n-\mu_A$.
-- source:
--   Li and Goldberg, Simple and explicit bounds for multi-server queues with 1/(1−ρ) scaling, arXiv:1706.04628v3, p. 25, Lemma 2 (with the coupling (7), p. 24)

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory

namespace GIGnBounds.Tail

/-- **Lemma 2** (Li–Goldberg, arXiv:1706.04628v3, p. 25). If `E[S] = 1` and `μ_A < n`, then for every
`x > 2` the supremum (4) is split into the arrival supremum (5) and the service supremum (6). `A_o` is
the ordinary renewal process of the later arrival intervals of the same family (coupling (7)). -/
theorem lemma_2 (n : ℕ) (μA μS : Measure ℝ) [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    (hA : IsTimeLaw μA) (hS : IsTimeLaw μS)
    (hS1 : mean μS = 1) (hstab : rate μA < n)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : RenewalFamily Ω P n μA μS) (x : ℝ) (hx : 2 < x) :
    P.real {ω | (x : EReal) ≤ supFrom (fun t => (F.Ae ω t : ℝ) - ∑ i, (F.Ne i ω t : ℝ))} ≤
      P.real {ω | ((1 / 2 * x - 1 : ℝ) : EReal) ≤
          supFrom (fun t => (F.Ao ω t : ℝ) - rate μA * t - 1 / 2 * (n - rate μA) * t)} +
        P.real {ω | ((1 / 2 * x : ℝ) : EReal) ≤
          supFrom (fun t => n * t - ∑ i, (F.Ne i ω t : ℝ) - 1 / 2 * (n - rate μA) * t)} := by sorry

end GIGnBounds.Tail
