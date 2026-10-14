-- Prove2me | Theorems.Thm_GIGnBounds_Tail_lemma_1
-- name    : GIGnBounds.Tail.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:40.428655+00:00
-- url     : https://prove2.me/theorems/f5e987f9-32c1-45f1-be94-d86839d31173
-- title:
--   Lemma 1 — $P(L(\infty)\ge x)\le P(\sup_{t\ge0}(A_e(t)-\sum_{i=1}^n N_{e,i}(t))\ge x)$
-- statement:
--   Consider the FCFS GI/GI/$n$ queue ($n\ge1$) with inter-arrival law $\mu_A$ and service law $\mu_S$, where $\mu_A<n\mu_S$ and $Q(\infty)$ exists with law $\pi$; $L(\infty)=\max(0,Q(\infty)-n)$. Here $(\Omega,\mathcal F,\mathbb P)$ is any probability space carrying a **bounding family**: an equilibrium renewal process $\mathcal A_e$ with renewals distributed as $A$ (first interval distributed as $R(A)$), and $n$ equilibrium renewal processes $\mathcal N_{e,1},\dots,\mathcal N_{e,n}$ with renewals distributed as $S$ (first interval $R(S)$), all intervals of all processes mutually independent. $A_e(t)$ and $N_{e,i}(t)$ are their numbers of renewals in $[0,t]$.
--
--   **Lemma 1** (Gamarnik and Goldberg). For every $x>0$,
--
--   $$\mathbb P\big(L(\infty)\ge x\big)\le \mathbb P\Big(\sup_{t\ge0}\Big(A_e(t)-\sum_{i=1}^n N_{e,i}(t)\Big)\ge x\Big).$$
--
--   This stochastic comparison reduces the steady-state queue to the supremum of a one-dimensional process built from independent renewal processes; the whole bound for $L(\infty)$ rests on it.
--
--   **Formalization Note.** The bound is asserted for every bounding family on every probability space (Ω in `Type`). The supremum is in the extended reals.
-- source:
--   Li and Goldberg, Simple and explicit bounds for multi-server queues with 1/(1−ρ) scaling, arXiv:1706.04628v3, p. 24, Lemma 1

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory

namespace GIGnBounds.Tail

/-- **Lemma 1** (Gamarnik and Goldberg; Li–Goldberg, arXiv:1706.04628v3, p. 24). If `μ_A < n μ_S` and
`Q(∞)` exists (law `π`), then for every `x > 0`,
`P(L(∞) ≥ x) ≤ P(sup_{t ≥ 0} (A_e(t) − Σ_{i=1}^n N_{e,i}(t)) ≥ x)`, for any bounding family. -/
theorem lemma_1 (n : ℕ) (hn : 0 < n) (μA μS : Measure ℝ) [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    (hA : IsTimeLaw μA) (hS : IsTimeLaw μS)
    (hstab : rate μA < n * rate μS)
    (π : Measure ℕ) (hπ : IsSteadyStateLaw n μA μS π)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : RenewalFamily Ω P n μA μS) (x : ℝ) (hx : 0 < x) :
    π.real {q : ℕ | x ≤ ((q - n : ℕ) : ℝ)} ≤
      P.real {ω | (x : EReal) ≤ supFrom (fun t => (F.Ae ω t : ℝ) - ∑ i, (F.Ne i ω t : ℝ))} := by sorry

end GIGnBounds.Tail
