-- Prove2me | Theorems.Thm_LargeForkJoin_FluidLimit_lemma_4_5
-- name    : LargeForkJoin.FluidLimit.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:05.515337+00:00
-- url     : https://prove2.me/theorems/f0a396db-e06d-4202-848a-9d072c2f7c9c
-- title:
--   Lemma 4.5, p. 18 — pointwise fluid limit of the empty-start maximum queue
-- statement:
--   In the fork-join model started empty ($Q^{(N)}_{(\alpha,\beta)}(0)=0$), for every $t>0$,
--   $$
--   \frac{Q^{(N)}_{(\alpha,\beta)}(tN^3\log N)}{N\log N}\ \xrightarrow{\ \mathbb P\ }\ \big(\sqrt{2\alpha t}-\beta t\big)\mathbb 1\Big(t<\frac{\alpha}{2\beta^2}\Big)+\frac{\alpha}{2\beta}\mathbb 1\Big(t\ge\frac{\alpha}{2\beta^2}\Big)\qquad(N\to\infty).
--   $$
--
--   The limit rises like $\sqrt{2\alpha t}-\beta t$ until the switch time $\alpha/(2\beta^2)$ and then stays at the steady-state level $\alpha/(2\beta)$. It is the first argument of the maximum in the fluid limit (2.5).
--
--   **Formalization Note** Convergence in probability to a constant $c$ is written as $\mathbb P(|Z_N-c|>\epsilon)\to0$ for every $\epsilon>0$. Times are natural numbers; $Q(tN^3\log N)$ is evaluated at $\lfloor tN^3\log N\rfloor$, which is the paper's convention $Q(n)=Q(\lfloor n\rfloor)$ (p. 25). The model hypothesis bundles Assumption 2.1 ($\alpha,\beta>0$), the Bernoulli laws of Definitions 2.1–2.2, Assumption 2.2 and measurability. Three conventions are added and disclosed: the Bernoulli laws are imposed only for $N\ge N_0$ (for small $N$ the number $p^{(N)}$ may be negative); within each $N\ge N_0$ the arrival indicators, the service indicators and the initial-condition variables $U_i$ are mutually independent (the paper never states that $(U_i)$ is independent of arrivals and services, but its proofs use it); servers are indexed $0,\dots,N-1$ instead of $1,\dots,N$.
-- source:
--   Schol, Vlasiou & Zwart, Large fork-join queues with nearly deterministic arrival and service times, arXiv:1912.11661v3, p. 18, Lemma 4.5

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model

namespace LargeForkJoin.FluidLimit

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_4_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ForkJoin Ω) (α β : ℝ) (N₀ : ℕ) (hM : IsModel P M α β N₀) (t : ℝ) (ht : 0 < t) :
    ∀ ε > 0, Tendsto (fun N : ℕ => P {ω | ε <
      |maxQueueEmpty M N (tau N t) ω / scale N - fluidEmpty α β t|}) atTop (𝓝 0) := by sorry
end LargeForkJoin.FluidLimit
