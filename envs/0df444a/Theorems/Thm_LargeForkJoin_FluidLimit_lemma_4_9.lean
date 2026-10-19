-- Prove2me | Theorems.Thm_LargeForkJoin_FluidLimit_lemma_4_9
-- name    : LargeForkJoin.FluidLimit.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:14.383563+00:00
-- url     : https://prove2.me/theorems/f6558b35-4003-47b7-94f3-ad75e6dbf675
-- title:
--   Lemma 4.9, p. 23 — from the Gaussian approximation to the starting-position part of the queue
-- statement:
--   In the fork-join model with initial queue lengths $Q_i^{(N)}(0)=\lfloor r_NU_i\rfloor$, fix $t>0$ and let $X_1,\dots,X_N$ be i.i.d. standard normal variables independent of the $Q_i^{(N)}(0)$. Assume that, for some constant $c$ (the value $g(t,q(0))$ of "a certain function $g$"),
--   $$
--   \max_{i\le N}\left(\frac{\sqrt{\alpha t}\,X_i}{\sqrt{\log N}}+\frac{Q_i^{(N)}(0)}{N\log N}\right)\xrightarrow{\ \mathbb P\ }c\qquad(N\to\infty). \tag{4.17}
--   $$
--   Then
--   $$
--   \max_{i\le N}\frac{A^{(N)}(tN^3\log N)-S_i^{(N)}(tN^3\log N)+Q_i^{(N)}(0)}{N\log N}\xrightarrow{\ \mathbb P\ }c-\beta t\qquad(N\to\infty).
--   $$
--
--   This transfers the Gaussian computation of Lemma 4.4 to the second argument of the maximum (2.3), the part of the queue driven by the initial condition.
--
--   **Formalization Note** As $t$ is fixed, "$g(t,q(0))$ for a certain function $g$" is a real constant $c$. Hypothesis (4.17) is stated for the law of the pairs $(X_i,U_i)_{i\le N}$: $N$ independent copies of (standard normal) $\otimes$ (law of $U_1$). Convergence in probability to a constant $c$ is written as $\mathbb P(|Z_N-c|>\epsilon)\to0$ for every $\epsilon>0$. Times are natural numbers; $Q(tN^3\log N)$ is evaluated at $\lfloor tN^3\log N\rfloor$, which is the paper's convention $Q(n)=Q(\lfloor n\rfloor)$ (p. 25). The model hypothesis bundles Assumption 2.1 ($\alpha,\beta>0$), the Bernoulli laws of Definitions 2.1–2.2, Assumption 2.2 and measurability. Three conventions are added and disclosed: the Bernoulli laws are imposed only for $N\ge N_0$ (for small $N$ the number $p^{(N)}$ may be negative); within each $N\ge N_0$ the arrival indicators, the service indicators and the initial-condition variables $U_i$ are mutually independent (the paper never states that $(U_i)$ is independent of arrivals and services, but its proofs use it); servers are indexed $0,\dots,N-1$ instead of $1,\dots,N$.
-- source:
--   Schol, Vlasiou & Zwart, Large fork-join queues with nearly deterministic arrival and service times, arXiv:1912.11661v3, p. 23, Lemma 4.9 (4.17)

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model

namespace LargeForkJoin.FluidLimit

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_4_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ForkJoin Ω) (α β : ℝ) (N₀ : ℕ) (hM : IsModel P M α β N₀) (t c : ℝ) (ht : 0 < t)
    (h417 : ∀ ε > 0, Tendsto (fun N : ℕ =>
      gaussPairLaw P M N {w | ε < |gaussPairMax M α N t w - c|}) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun N : ℕ => P {ω | ε <
      |maxStartPart M N (tau N t) ω / scale N - (c - β * t)|}) atTop (𝓝 0) := by sorry
end LargeForkJoin.FluidLimit
