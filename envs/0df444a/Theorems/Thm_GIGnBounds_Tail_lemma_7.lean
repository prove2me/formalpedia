-- Prove2me | Theorems.Thm_GIGnBounds_Tail_lemma_7
-- name    : GIGnBounds.Tail.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:11.207264+00:00
-- url     : https://prove2.me/theorems/75d3f42b-2d51-43ca-b16b-747c888b5674
-- title:
--   Lemma 7 — $P(Q(\infty)-n\ge x)\le P(\sup_t(A_e(t)-\sum_{i=1}^{n'}N_{e,i}(t))\ge x+(n-n'))$
-- statement:
--   Consider the FCFS GI/GI/$n$ queue with inter-arrival law $\mu_A$ and service law $\mu_S$, where $\mu_A<n\mu_S$ and $Q(\infty)$ exists with law $\pi$. Fix $n'\in\{1,\dots,n\}$. Here $(\Omega,\mathcal F,\mathbb P)$ is any probability space carrying a **bounding family**: an equilibrium renewal process $\mathcal A_e$ with renewals distributed as $A$ (first interval distributed as $R(A)$), and $n'$ equilibrium renewal processes $\mathcal N_{e,1},\dots,\mathcal N_{e,n'}$ with renewals distributed as $S$ (first interval $R(S)$), all intervals of all processes mutually independent. $A_e(t)$ and $N_{e,i}(t)$ are their numbers of renewals in $[0,t]$.
--
--   **Lemma 7.** For all $n'\in\{1,\dots,n\}$ and $x\ge n'-n$,
--
--   $$\mathbb P\big(Q(\infty)-n\ge x\big)\le\mathbb P\Big(\sup_{t\ge0}\Big(A_e(t)-\sum_{i=1}^{n'}N_{e,i}(t)\Big)\ge x+(n-n')\Big).$$
--
--   Comparing the $n$-server queue with an $n'$-server bounding process makes the comparison informative at the level $Q(\infty)\ge n$, where Lemma 1 is trivial.
--
--   **Formalization Note.** $Q(\infty)-n$ is not truncated here ($x$ may be negative).
-- source:
--   Li and Goldberg, Simple and explicit bounds for multi-server queues with 1/(1−ρ) scaling, arXiv:1706.04628v3, p. 28, Lemma 7

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory

namespace GIGnBounds.Tail

/-- **Lemma 7** (Li–Goldberg, arXiv:1706.04628v3, p. 28). If `μ_A < n μ_S` and `Q(∞)` exists (law `π`),
then for all `n' ∈ {1, …, n}` and `x ≥ n' − n`,
`P(Q(∞) − n ≥ x) ≤ P(sup_{t≥0} (A_e(t) − Σ_{i=1}^{n'} N_{e,i}(t)) ≥ x + (n − n'))`, for any bounding
family with `n'` service processes. -/
theorem lemma_7 (n : ℕ) (hn : 0 < n) (μA μS : Measure ℝ) [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    (hA : IsTimeLaw μA) (hS : IsTimeLaw μS)
    (hstab : rate μA < n * rate μS)
    (π : Measure ℕ) (hπ : IsSteadyStateLaw n μA μS π)
    (n' : ℕ) (hn'₁ : 1 ≤ n') (hn'₂ : n' ≤ n) (x : ℝ) (hx : (n' : ℝ) - n ≤ x)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : RenewalFamily Ω P n' μA μS) :
    π.real {q : ℕ | x ≤ (q : ℝ) - n} ≤
      P.real {ω | ((x + ((n : ℝ) - n') : ℝ) : EReal) ≤ supFrom (fun t => (F.Ae ω t : ℝ) - ∑ i, (F.Ne i ω t : ℝ))} := by sorry

end GIGnBounds.Tail
