-- Prove2me | Theorems.Thm_LargeForkJoin_FluidLimit_lemma_4_8
-- name    : LargeForkJoin.FluidLimit.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:17.203014+00:00
-- url     : https://prove2.me/theorems/dcf00b69-eed2-47c6-83e6-ea088bcb6f31
-- title:
--   Lemma 4.8, p. 22 — lower bound of the empty-start maximum queue
-- statement:
--   In the fork-join model started empty ($Q^{(N)}_{(\alpha,\beta)}(0)=0$), let $\delta>0$ and $t\ge0$. Then
--   $$
--   \liminf_{N\to\infty}\mathbb P\left(\frac{Q^{(N)}_{(\alpha,\beta)}(tN^3\log N)}{N\log N}\ge\big(\sqrt{2\alpha t}-\beta t\big)\mathbb 1\Big(t<\frac{\alpha}{2\beta^2}\Big)+\frac{\alpha}{2\beta}\mathbb 1\Big(t\ge\frac{\alpha}{2\beta^2}\Big)-\delta\right)=1 .
--   $$
--
--   This is the lower half of the pointwise fluid limit of the empty-start system (Lemma 4.5).
--
--   **Formalization Note** Since probabilities are at most $1$, "liminf $=1$" is written as convergence of the probabilities to $1$. The page states no range for $t$; $t\ge0$ (a time of the process) is stated. The model hypothesis bundles Assumption 2.1 ($\alpha,\beta>0$), the Bernoulli laws of Definitions 2.1–2.2, Assumption 2.2 and measurability. Three conventions are added and disclosed: the Bernoulli laws are imposed only for $N\ge N_0$ (for small $N$ the number $p^{(N)}$ may be negative); within each $N\ge N_0$ the arrival indicators, the service indicators and the initial-condition variables $U_i$ are mutually independent (the paper never states that $(U_i)$ is independent of arrivals and services, but its proofs use it); servers are indexed $0,\dots,N-1$ instead of $1,\dots,N$.
-- source:
--   Schol, Vlasiou & Zwart, Large fork-join queues with nearly deterministic arrival and service times, arXiv:1912.11661v3, p. 22, Lemma 4.8 (4.16)

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model

namespace LargeForkJoin.FluidLimit

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_4_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ForkJoin Ω) (α β : ℝ) (N₀ : ℕ) (hM : IsModel P M α β N₀) (δ t : ℝ) (hδ : 0 < δ)
    (ht : 0 ≤ t) :
    Tendsto (fun N : ℕ => P {ω | fluidEmpty α β t - δ ≤
      maxQueueEmpty M N (tau N t) ω / scale N}) atTop (𝓝 1) := by sorry
end LargeForkJoin.FluidLimit
