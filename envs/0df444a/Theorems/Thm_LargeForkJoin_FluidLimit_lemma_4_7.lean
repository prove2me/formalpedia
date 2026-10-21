-- Prove2me | Theorems.Thm_LargeForkJoin_FluidLimit_lemma_4_7
-- name    : LargeForkJoin.FluidLimit.lemma_4_7
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-20T13:11:19.973162+00:00
-- url     : https://prove2.me/theorems/82bed8dc-3428-4998-b422-e6595d5b100d
-- title:
--   Lemma 4.7, p. 21 — upper bound of the empty-start maximum queue after the switch time
-- statement:
--   **Upper bound of the empty-start maximum queue after the switch time.**
--
--   Consider the $N$-server fork-join queue of the mission model (Bernoulli arrivals with probability $p^{(N)}=1-\alpha/N-\beta/N^2$, Bernoulli services with probability $q^{(N)}=1-\alpha/N$, $\alpha,\beta>0$), started empty: $Q^{(N)}_{(\alpha,\beta)}(0)=0$, so that the maximum queue length is
--   $$Q^{(N)}_{(\alpha,\beta)}(n)=\max_{i\le N}\sup_{0\le k\le n}\big[(A^{(N)}(n)-A^{(N)}(k))-(S^{(N)}_i(n)-S^{(N)}_i(k))\big].$$
--   Then for every $\delta>0$ and every $t\ge \alpha/(2\beta^2)$,
--   $$\limsup_{N\to\infty}\mathbb P\left(\frac{Q^{(N)}_{(\alpha,\beta)}(tN^3\log N)}{N\log N}>\frac{\alpha}{2\beta}+\delta\right)=0.$$
--
--   Together with Lemma 4.6 (the upper bound for $t<\alpha/(2\beta^2)$) and Lemma 4.8 (the lower bound), this gives the pointwise fluid limit of Lemma 4.5.
--
--   **Formalization note.** Since the probabilities are non-negative, "$\limsup = 0$" is stated as convergence to $0$. The time $tN^3\log N$ is evaluated at $\lfloor tN^3\log N\rfloor$ (`tau N t`), the empty-start maximum is `maxQueueEmpty`, and the scaling $N\log N$ is `scale N`, all from the mission's model definition. The paper's condition reads $\alpha/(2\beta^2)\le t<\infty$.
-- source:
--   Schol, Vlasiou & Zwart, Large fork-join queues with nearly deterministic arrival and service times, arXiv:1912.11661v3, p. 21, Lemma 4.7

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model

namespace LargeForkJoin.FluidLimit

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_4_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ForkJoin Ω) (α β : ℝ) (N₀ : ℕ) (hM : IsModel P M α β N₀) (δ t : ℝ) (hδ : 0 < δ)
    (ht : α / (2 * β ^ 2) ≤ t) :
    Tendsto (fun N : ℕ => P {ω | α / (2 * β) + δ <
      maxQueueEmpty M N (tau N t) ω / scale N}) atTop (𝓝 0) := by sorry
end LargeForkJoin.FluidLimit
