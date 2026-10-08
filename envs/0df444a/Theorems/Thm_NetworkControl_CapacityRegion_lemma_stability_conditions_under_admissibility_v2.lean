-- Prove2me | Theorems.Thm_NetworkControl_CapacityRegion_lemma_stability_conditions_under_admissibility_v2
-- name    : NetworkControl.CapacityRegion.lemma_stability_conditions_under_admissibility_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:21:08.125989+00:00
-- url     : https://prove2.me/theorems/7d80c9c3-81c6-445b-addb-f5977cb74032
-- title:
--   Lemma 3.6 — stability conditions under admissible arrivals and service (corrected: history filtration)
-- statement:
--   Consider a single discrete-time queue on a filtered probability space $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge 0},\mathbb P)$ with backlog
--   $$U(t+1)=\max[U(t)-\mu(t),0]+A(t),\qquad U(0)=U_0\ge 0,\ \mathbb E\,U_0<\infty,$$
--   where the arrivals $A(t)\ge 0$ and the service opportunities $\mu(t)\ge 0$ of slot $t$ are $\mathcal F_{t+1}$-measurable and $U_0$ is $\mathcal F_0$-measurable, so that $\mathcal F_t$ contains the history $H(t)$ of all arrival, service and backlog events of slots $0,\dots,t-1$. Suppose $A$ is an *admissible arrival process* of rate $\lambda$ (Definition 3.4: time-average expected rate $\lambda$, uniformly bounded conditional second moments given $\mathcal F_t$, and for every $\delta>0$ a window $T$ with $\mathbb E\{\tfrac1T\sum_{k<T}A(t_0+k)\mid\mathcal F_{t_0}\}\le\lambda+\delta$ for all $t_0$) and $\mu$ is an *admissible server process* of rate $\mu$ (Definition 3.5, with the symmetric lower bound $\ge\mu-\delta$ and a uniform upper bound $\mu_{\max}$). Then
--
--   1. if the queue is strongly stable, i.e. $\limsup_{t\to\infty}\frac1t\sum_{\tau<t}\mathbb E\,U(\tau)<\infty$, then $\lambda\le\mu$;
--   2. if $\lambda<\mu$, then the queue is strongly stable.
--
--   **Formalization Note.** The retired statement quantified over an arbitrary filtration $\mathcal F$ with nothing tying $A$, $\mu$, $U_0$ to it; with the trivial filtration the conditional admissibility bounds collapsed to plain expectations, and a server anti-correlated with the sample path satisfied "admissibility" while starving the queue on half of the paths (the accepted disproof). The corrected statement makes the processes adapted — $A(t),\mu(t)$ are $\mathcal F_{t+1}$-measurable and $U_0$ is $\mathcal F_0$-measurable, so $U(t)$ is $\mathcal F_t$-measurable and $\mathcal F_t\supseteq H(t)$ — which is exactly how the monograph's conditioning on the history $H(t)$ reads. Nonnegativity of arrivals, services and the initial backlog and $\mathbb E\,U(0)<\infty$ are the monograph's standing conventions for queues and are stated explicitly; integrability of $U(t)$ for every $t$ then follows from $U(t)\le U_0+\sum_{\tau<t}A(\tau)$ and is not assumed. Strong stability is `StronglyStable` (Definition 3.1 in its bounded-Cesàro-average form, equivalent to $\limsup<\infty$ for a real sequence).
-- source:
--   Georgiadis, Neely & Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Foundations and Trends in Networking 1(1), 2006, p. 26, Lemma 3.6 (with Definitions 3.4, 3.5, p. 25-26, and the queueing law of §3.1, p. 23)

import Mathlib
import Definitions.Def_NetworkControl_CapacityRegion_QueueBacklog
import Definitions.Def_NetworkControl_CapacityRegion_AdmissibleArrival
import Definitions.Def_NetworkControl_CapacityRegion_AdmissibleService
import Definitions.Def_NetworkControl_CapacityRegion_StronglyStable

namespace NetworkControl.CapacityRegion

open MeasureTheory

/-- Lemma 3.6 (Stability Conditions under Admissibility), Georgiadis–Neely–Tassiulas p. 26.
A single queue `U(t+1) = max[U(t) - μ(t), 0] + A(t)` (`QueueBacklog`) is fed by an admissible
arrival process `A` of rate `lam` (Definition 3.4) and served by an admissible server process
`svc` of rate `mu` (Definition 3.5), both conditions being taken with respect to the history
`H(t)` of the system. Then (a) `lam ≤ mu` is necessary for strong stability of the queue, and (b)
`lam < mu` is sufficient.

Corrected version: the filtration `𝓕` is tied to the processes — arrivals and services of slot
`t` and the initial backlog are measurable with respect to `𝓕 (t+1)` and `𝓕 0` respectively, so
`𝓕 t` contains the history `H(t)` of slots `0,…,t-1` (the retired version left `𝓕` free, so the
trivial filtration turned the conditional admissibility bounds into plain expectations). Arrivals,
services and the initial backlog are nonnegative, and `E U(0) < ∞`, as throughout the monograph. -/
theorem lemma_stability_conditions_under_admissibility_v2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ mΩ) (A svc : ℕ → Ω → ℝ) (U0 : Ω → ℝ) (lam mu : ℝ)
    (hU0meas : Measurable[𝓕 0] U0) (hU0nn : ∀ ω, 0 ≤ U0 ω) (hU0int : Integrable U0 P)
    (hAadapt : ∀ t : ℕ, Measurable[𝓕 (t + 1)] (A t)) (hAnn : ∀ t ω, 0 ≤ A t ω)
    (hsvcadapt : ∀ t : ℕ, Measurable[𝓕 (t + 1)] (svc t)) (hsvcnn : ∀ t ω, 0 ≤ svc t ω)
    (hA : AdmissibleArrival P 𝓕 A lam)
    (hsvc : AdmissibleService P 𝓕 svc mu) :
    (StronglyStable (fun t : ℕ => ∫ ω, QueueBacklog A svc U0 t ω ∂P) → lam ≤ mu) ∧
      (lam < mu → StronglyStable (fun t : ℕ => ∫ ω, QueueBacklog A svc U0 t ω ∂P)) := by sorry

end NetworkControl.CapacityRegion
