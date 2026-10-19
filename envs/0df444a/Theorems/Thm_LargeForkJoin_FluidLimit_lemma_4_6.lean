-- Prove2me | Theorems.Thm_LargeForkJoin_FluidLimit_lemma_4_6
-- name    : LargeForkJoin.FluidLimit.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:03.078671+00:00
-- url     : https://prove2.me/theorems/1955cd18-de6a-48b9-a5bb-a4edc12d1bef
-- title:
--   Lemma 4.6, p. 18 — upper bound of the empty-start maximum queue before the switch time
-- statement:
--   In the fork-join model started empty ($Q^{(N)}_{(\alpha,\beta)}(0)=0$), let $\delta>0$ and $0\le t<\alpha/(2\beta^2)$. Then
--   $$
--   \limsup_{N\to\infty}\mathbb P\left(\frac{Q^{(N)}_{(\alpha,\beta)}(tN^3\log N)}{N\log N}>\sqrt{2\alpha t}-\beta t+\delta\right)=0 .
--   $$
--
--   Before the switch time $\alpha/(2\beta^2)$ the scaled maximum queue does not exceed the increasing branch $\sqrt{2\alpha t}-\beta t$ of the fluid limit; this is the upper half of Lemma 4.5 on that range.
--
--   **Formalization Note** "limsup of probabilities $=0$" is written as convergence of the probabilities to $0$ (they are non-negative). The time $t$ is a time of the process, so $t\ge0$ is stated; the page writes only $t<\alpha/(2\beta^2)$. The maximum queue is that of (2.1), the system started empty. The model hypothesis bundles Assumption 2.1 ($\alpha,\beta>0$), the Bernoulli laws of Definitions 2.1–2.2, Assumption 2.2 and measurability. Three conventions are added and disclosed: the Bernoulli laws are imposed only for $N\ge N_0$ (for small $N$ the number $p^{(N)}$ may be negative); within each $N\ge N_0$ the arrival indicators, the service indicators and the initial-condition variables $U_i$ are mutually independent (the paper never states that $(U_i)$ is independent of arrivals and services, but its proofs use it); servers are indexed $0,\dots,N-1$ instead of $1,\dots,N$.
-- source:
--   Schol, Vlasiou & Zwart, Large fork-join queues with nearly deterministic arrival and service times, arXiv:1912.11661v3, p. 18, Lemma 4.6 (4.11)

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model

namespace LargeForkJoin.FluidLimit

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_4_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ForkJoin Ω) (α β : ℝ) (N₀ : ℕ) (hM : IsModel P M α β N₀) (δ t : ℝ) (hδ : 0 < δ)
    (ht0 : 0 ≤ t) (ht : t < α / (2 * β ^ 2)) :
    Tendsto (fun N : ℕ => P {ω | Real.sqrt (2 * α * t) - β * t + δ <
      maxQueueEmpty M N (tau N t) ω / scale N}) atTop (𝓝 0) := by sorry
end LargeForkJoin.FluidLimit
