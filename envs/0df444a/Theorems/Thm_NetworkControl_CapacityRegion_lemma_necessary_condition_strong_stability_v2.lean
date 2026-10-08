-- Prove2me | Theorems.Thm_NetworkControl_CapacityRegion_lemma_necessary_condition_strong_stability_v2
-- name    : NetworkControl.CapacityRegion.lemma_necessary_condition_strong_stability_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:20:55.639894+00:00
-- url     : https://prove2.me/theorems/f7864cca-bff2-4d10-82b2-9c2fb7ef551d
-- title:
--   Lemma 3.3 — necessary condition for strong stability (corrected: stated for the queue process)
-- statement:
--   Let $U(t)$ be the backlog of a discrete-time queue $U(t+1)=\max[U(t)-\mu(t),0]+A(t)$ on a probability space, with nonnegative integrable arrivals $A(t)$, nonnegative integrable service $\mu(t)$ and nonnegative initial backlog $U(0)$ of finite mean. Suppose the queue is strongly stable, $\limsup_{t\to\infty}\frac1t\sum_{\tau<t}\mathbb E\,U(\tau)<\infty$, and that either $\mathbb E\,A(t)\le A_{\max}$ for all $t$ or $\mathbb E\{\mu(t)-A(t)\}\le D_{\max}$ for all $t$, for finite constants $A_{\max},D_{\max}\ge 0$. Then
--   $$\lim_{t\to\infty}\frac{\mathbb E\,U(t)}{t}=0.$$
--
--   **Formalization Note.** The retired statement took the expected backlog as a free real sequence $U$ with no link to $A$ and $\mu$; since strong stability is only an upper bound on Cesàro averages, $U(t)=-t$ satisfied every hypothesis while $U(t)/t\to-1$ (the accepted disproof). The corrected statement is about the queue itself (`QueueBacklog`), whose law gives $U(t)\ge 0$ and $U(t)-\mu(t)+A(t)\le U(t+1)\le U(t)+A(t)$ — the two inequalities the monograph's proof uses. Nonnegativity of arrivals and services and $\mathbb E\,U(0)<\infty$ are the standing conventions; integrability of $U(t)$ follows from them and is not assumed.
-- source:
--   Georgiadis, Neely & Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Foundations and Trends in Networking 1(1), 2006, p. 24, Lemma 3.3 (Necessary Condition for Strong Stability), with the queueing law of §3.1, p. 23

import Mathlib
import Definitions.Def_NetworkControl_CapacityRegion_QueueBacklog
import Definitions.Def_NetworkControl_CapacityRegion_StronglyStable

namespace NetworkControl.CapacityRegion

open MeasureTheory

/-- Lemma 3.3 (Necessary Condition for Strong Stability), Georgiadis–Neely–Tassiulas p. 24.
Let `U(t)` be the backlog of a queue `U(t+1) = max[U(t) - μ(t), 0] + A(t)` with nonnegative
arrivals `A(t)`, nonnegative service `μ(t)` and nonnegative initial backlog `U(0)` of finite mean.
If the queue is strongly stable, and either `E A(t) ≤ Amax` for all `t` or
`E{μ(t) - A(t)} ≤ Dmax` for all `t` (with `Amax, Dmax` finite), then `E U(t)/t → 0`.

Corrected version: `U` is the backlog process of the queue (`QueueBacklog`), not a free real
sequence — the retired version lost the queueing law (and the nonnegativity of backlogs) that
links `U` to `A` and `μ`, so the arrival/service bounds constrained nothing. -/
theorem lemma_necessary_condition_strong_stability_v2
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (A svc : ℕ → Ω → ℝ) (U0 : Ω → ℝ)
    (hAnn : ∀ t ω, 0 ≤ A t ω) (hsvcnn : ∀ t ω, 0 ≤ svc t ω) (hU0nn : ∀ ω, 0 ≤ U0 ω)
    (hU0int : Integrable U0 P) (hAint : ∀ t, Integrable (A t) P)
    (hsvcint : ∀ t, Integrable (svc t) P)
    (Amax Dmax : ℝ) (hAmax : 0 ≤ Amax) (hDmax : 0 ≤ Dmax)
    (hstable : StronglyStable (fun t : ℕ => ∫ ω, QueueBacklog A svc U0 t ω ∂P))
    (hbound : (∀ t : ℕ, ∫ ω, A t ω ∂P ≤ Amax) ∨
      (∀ t : ℕ, ∫ ω, (svc t ω - A t ω) ∂P ≤ Dmax)) :
    Filter.Tendsto (fun t : ℕ => (∫ ω, QueueBacklog A svc U0 t ω ∂P) / (t : ℝ))
      Filter.atTop (nhds 0) := by sorry

end NetworkControl.CapacityRegion
