-- Prove2me | Theorems.Thm_GIGnBounds_Tail_lemma_14
-- name    : GIGnBounds.Tail.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:22.311987+00:00
-- url     : https://prove2.me/theorems/c64e80c9-31e2-4eb3-a55f-042e0b1e4372
-- title:
--   Lemma 14 — $P(Q^{n'}_{res}(t)-n'\ge x)\le P(\sup_{0\le s\le t}(A_e(s)-\sum_{i=1}^{n'}N_{e,i}(s))\ge x)$
-- statement:
--   Let $m\ge1$ and let $\mathcal Q^{m}_{\mathrm{res}}$ be the FCFS GI/GI/$m$ queue with inter-arrival law $\mu_A$ and service law $\mu_S$ started as follows: the time until the first arrival is distributed as $R(A)$, and all $m$ servers hold a job whose residual service times are i.i.d. distributed as $R(S)$, independent of the arrival process. $Q^m_{\mathrm{res}}(t)$ is its number in system at time $t$. Assume $0<\mathbb E[A],\mathbb E[S]<\infty$. Here $(\Omega,\mathcal F,\mathbb P)$ is any probability space carrying a **bounding family**: an equilibrium renewal process $\mathcal A_e$ with renewals distributed as $A$ (first interval distributed as $R(A)$), and $m$ equilibrium renewal processes $\mathcal N_{e,1},\dots,\mathcal N_{e,m}$ with renewals distributed as $S$ (first interval $R(S)$), all intervals of all processes mutually independent. $A_e(t)$ and $N_{e,i}(t)$ are their numbers of renewals in $[0,t]$.
--
--   **Lemma 14** (Gamarnik and Goldberg). For all $t,x>0$,
--
--   $$\mathbb P\big(Q^{m}_{\mathrm{res}}(t)-m\ge x\big)\le\mathbb P\Big(\sup_{0\le s\le t}\Big(A_e(s)-\sum_{i=1}^{m}N_{e,i}(s)\Big)\ge x\Big).$$
--
--   It is the transient comparison from which Lemma 7 is derived; it needs no stability or steady-state assumption.
--
--   **Formalization Note.** The paper writes $n'$ for the number of servers; here it is $m$, and $m\ge1$ as in the paper's range $n'\in\{1,\dots,n\}$.
-- source:
--   Li and Goldberg, Simple and explicit bounds for multi-server queues with 1/(1−ρ) scaling, arXiv:1706.04628v3, p. 36, Lemma 14 (system 𝒬^{n′}_res defined on p. 36)

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory

namespace GIGnBounds.Tail

/-- **Lemma 14** (Gamarnik and Goldberg; Li–Goldberg, arXiv:1706.04628v3, p. 36). Let `𝒬^{m}_res` be the
FCFS GI/GI/m queue whose first arrival is distributed as `R(A)` and whose `m` servers are all busy at
time 0 with i.i.d. residual service times distributed as `R(S)`, independent of the arrivals. If
`0 < E[A], E[S] < ∞`, then for all `t, x > 0`,
`P(Q^{m}_res(t) − m ≥ x) ≤ P(sup_{0≤s≤t} (A_e(s) − Σ_{i=1}^m N_{e,i}(s)) ≥ x)`. -/
theorem lemma_14 (m : ℕ) (hm : 0 < m) (μA μS : Measure ℝ) [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    (hA : IsTimeLaw μA) (hS : IsTimeLaw μS)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : RenewalFamily Ω P m μA μS) (t x : ℝ) (ht : 0 < t) (hx : 0 < x) :
    (queueMeasure m μA μS (resInit m μA μS)).real {ω | x ≤ (queueLength ω t : ℝ) - m} ≤
      P.real {ω | (x : EReal) ≤ supUpTo (fun s => (F.Ae ω s : ℝ) - ∑ i, (F.Ne i ω s : ℝ)) t} := by sorry

end GIGnBounds.Tail
