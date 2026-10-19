-- Prove2me | Theorems.Thm_LargeForkJoin_FluidLimit_lemma_4_3
-- name    : LargeForkJoin.FluidLimit.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:16.562358+00:00
-- url     : https://prove2.me/theorems/f6ee1363-b736-4525-98b0-a1a8776df4fd
-- title:
--   Lemma 4.3, p. 17 — limsup of the 5/2-moment of the maximum of ±S̃_i/log N
-- statement:
--   In the fork-join model, fix $t>0$ and let $\tilde S_i^{(N)}$ be the centred service process of Definition 4.1. Then
--   $$
--   \limsup_{N\to\infty}\mathbb E\left[\max\left(\max_{i\le N}\frac{\pm\tilde S_i^{(N)}(tN^3\log N)}{\log N},\,0\right)^{5/2}\right]\le(2\alpha t)^{5/4},
--   $$
--   for both choices of the sign.
--
--   The maximum of $N$ centred service processes, scaled by $\log N$, is of order $\sqrt{2\alpha t}$; the lemma controls its $5/2$-th moment, which enters Doob's maximal inequality in the tightness proofs.
--
--   **Formalization Note** The limsup is written as: for every $\epsilon>0$, eventually in $N$ the expectation is at most $(2\alpha t)^{5/4}+\epsilon$. The base of the power is non-negative, so the real power is the usual one. For $N\ge N_0$ the variable is bounded, so the expectation is a genuine (finite) integral. The model hypothesis bundles Assumption 2.1 ($\alpha,\beta>0$), the Bernoulli laws of Definitions 2.1–2.2, Assumption 2.2 and measurability. Three conventions are added and disclosed: the Bernoulli laws are imposed only for $N\ge N_0$ (for small $N$ the number $p^{(N)}$ may be negative); within each $N\ge N_0$ the arrival indicators, the service indicators and the initial-condition variables $U_i$ are mutually independent (the paper never states that $(U_i)$ is independent of arrivals and services, but its proofs use it); servers are indexed $0,\dots,N-1$ instead of $1,\dots,N$.
-- source:
--   Schol, Vlasiou & Zwart, Large fork-join queues with nearly deterministic arrival and service times, arXiv:1912.11661v3, p. 17, Lemma 4.3 (4.9)

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model

namespace LargeForkJoin.FluidLimit

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_4_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ForkJoin Ω) (α β : ℝ) (N₀ : ℕ) (hM : IsModel P M α β N₀) (t : ℝ) (ht : 0 < t) :
    (∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      ∫ ω, (max (⨆ i : Fin N, Stil M α N i (tau N t) ω / Real.log N) 0) ^ (5 / 2 : ℝ) ∂P ≤
        (2 * α * t) ^ (5 / 4 : ℝ) + ε) ∧
    (∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      ∫ ω, (max (⨆ i : Fin N, -Stil M α N i (tau N t) ω / Real.log N) 0) ^ (5 / 2 : ℝ) ∂P ≤
        (2 * α * t) ^ (5 / 4 : ℝ) + ε) := by sorry
end LargeForkJoin.FluidLimit
