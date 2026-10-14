-- Prove2me | Theorems.Thm_GIGnBounds_Tail_corollary_5
-- name    : GIGnBounds.Tail.corollary_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:23.470992+00:00
-- url     : https://prove2.me/theorems/cda2b81a-c4b2-4855-8756-d559d3c52381
-- title:
--   Corollary 5 — $P(Q(\infty)\ge n)$ bounded via $n-\lfloor\frac12(n-\mu_A)\rfloor$ servers
-- statement:
--   Under the assumptions of Lemma 7 ($\mu_A<n\mu_S$, $Q(\infty)$ exists with law $\pi$), and with $\mathbb E[S]=1$, put $k=\lfloor\tfrac12(n-\mu_A)\rfloor$. Here $(\Omega,\mathcal F,\mathbb P)$ is any probability space carrying a **bounding family**: an equilibrium renewal process $\mathcal A_e$ with renewals distributed as $A$ (first interval distributed as $R(A)$), and $n-k$ equilibrium renewal processes $\mathcal N_{e,1},\dots,\mathcal N_{e,n-k}$ with renewals distributed as $S$ (first interval $R(S)$), all intervals of all processes mutually independent. $A_e(t)$ and $N_{e,i}(t)$ are their numbers of renewals in $[0,t]$.
--
--   **Corollary 5.**
--
--   $$\mathbb P\big(Q(\infty)\ge n\big)\le\mathbb P\Big(\sup_{t\ge0}\Big(A_e(t)-\sum_{i=1}^{n-\lfloor\frac12(n-\mu_A)\rfloor}N_{e,i}(t)\Big)\ge\Big\lfloor\frac12(n-\mu_A)\Big\rfloor\Big).$$
--
--   It reduces the steady-state probability of delay to a tail of the bounding process with fewer servers, to which the display of p. 28 applies.
--
--   **Formalization Note.** Since $n-\mu_A>0$ the floor is a natural number, and $n-k\ge1$.
-- source:
--   Li and Goldberg, Simple and explicit bounds for multi-server queues with 1/(1−ρ) scaling, arXiv:1706.04628v3, p. 28, Corollary 5

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory

namespace GIGnBounds.Tail

/-- **Corollary 5** (Li–Goldberg, arXiv:1706.04628v3, p. 28). Under the assumptions of Lemma 7 and
`E[S] = 1`, with `k = ⌊½(n − μ_A)⌋`,
`P(Q(∞) ≥ n) ≤ P(sup_{t≥0} (A_e(t) − Σ_{i=1}^{n−k} N_{e,i}(t)) ≥ k)`, for any bounding family with
`n − k` service processes. -/
theorem corollary_5 (n : ℕ) (hn : 0 < n) (μA μS : Measure ℝ) [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    (hA : IsTimeLaw μA) (hS : IsTimeLaw μS)
    (hS1 : mean μS = 1) (hstab : rate μA < n * rate μS)
    (π : Measure ℕ) (hπ : IsSteadyStateLaw n μA μS π)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : RenewalFamily Ω P (n - ⌊(1 / 2 : ℝ) * (n - rate μA)⌋₊) μA μS) :
    π.real {q : ℕ | n ≤ q} ≤
      P.real {ω | ((⌊(1 / 2 : ℝ) * (n - rate μA)⌋₊ : ℝ) : EReal) ≤ supFrom (fun t => (F.Ae ω t : ℝ) - ∑ i, (F.Ne i ω t : ℝ))} := by sorry

end GIGnBounds.Tail
