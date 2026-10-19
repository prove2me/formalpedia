-- Prove2me | Theorems.Thm_LargeForkJoin_FluidLimit_lemma_4_2
-- name    : LargeForkJoin.FluidLimit.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:03.967335+00:00
-- url     : https://prove2.me/theorems/b7573816-bc60-45da-8299-84ab5e814c54
-- title:
--   Lemma 4.2, p. 17 — non-uniform Berry–Esseen rate for the standardized service process M_i(t)
-- statement:
--   In the fork-join model with $p^{(N)}=1-\alpha/N-\beta/N^2$ and $q^{(N)}=1-\alpha/N$, let $t>0$ and let
--   $$
--   M_i^{(N)}(t)=\frac{\tilde S_i^{(N)}(tN^3\log N)}{\sqrt{\alpha t(1-\alpha/N)\log N}}\cdot\frac{\sqrt{tN^3\log N}}{\sqrt{\lfloor tN^3\log N\rfloor}}
--   $$
--   be the standardized centred service process of server $i$ (Definition 4.1, (4.4)). Let $\Phi$ be the standard normal distribution function. There is a constant $c_t>0$ such that, for all large $N$, all servers $i$ and all $y\in\mathbb R$,
--   $$
--   \Big|\mathbb P\big(M_i^{(N)}(t)<y\big)-\Phi(y)\Big|\le\frac{c_t}{N\sqrt{\log N}}\cdot\frac{1}{1+|y|^3},
--   $$
--   and the same bound holds with $-M_i^{(N)}(t)$ in place of $M_i^{(N)}(t)$.
--
--   This rate, of non-uniform Berry–Esseen type, is what allows the paper to replace the service processes of $N$ servers by Gaussian variables inside a maximum over $N$ servers.
--
--   **Formalization Note** The "$\pm$" of the paper is rendered as two inequalities. The page states no lower bound on $N$; the Lean statement asks for the bound for all $N\ge N_1$ with some $N_1$, which is necessary because $\log 1=0$ makes the right side meaningless at $N=1$. The model hypothesis bundles Assumption 2.1 ($\alpha,\beta>0$), the Bernoulli laws of Definitions 2.1–2.2, Assumption 2.2 and measurability. Three conventions are added and disclosed: the Bernoulli laws are imposed only for $N\ge N_0$ (for small $N$ the number $p^{(N)}$ may be negative); within each $N\ge N_0$ the arrival indicators, the service indicators and the initial-condition variables $U_i$ are mutually independent (the paper never states that $(U_i)$ is independent of arrivals and services, but its proofs use it); servers are indexed $0,\dots,N-1$ instead of $1,\dots,N$.
-- source:
--   Schol, Vlasiou & Zwart, Large fork-join queues with nearly deterministic arrival and service times, arXiv:1912.11661v3, p. 17, Lemma 4.2 (4.8)

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model

namespace LargeForkJoin.FluidLimit

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_4_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ForkJoin Ω) (α β : ℝ) (N₀ : ℕ) (hM : IsModel P M α β N₀) (t : ℝ) (ht : 0 < t) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ i : Fin N, ∀ y : ℝ,
      |(P {ω | Mstd M α N i t ω < y}).toReal - cdf (gaussianReal 0 1) y| ≤
          c / (N * Real.sqrt (Real.log N)) * (1 / (1 + |y| ^ 3)) ∧
      |(P {ω | -Mstd M α N i t ω < y}).toReal - cdf (gaussianReal 0 1) y| ≤
          c / (N * Real.sqrt (Real.log N)) * (1 / (1 + |y| ^ 3)) := by sorry
end LargeForkJoin.FluidLimit
