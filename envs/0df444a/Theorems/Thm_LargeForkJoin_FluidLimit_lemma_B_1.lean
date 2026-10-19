-- Prove2me | Theorems.Thm_LargeForkJoin_FluidLimit_lemma_B_1
-- name    : LargeForkJoin.FluidLimit.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:07.087655+00:00
-- url     : https://prove2.me/theorems/e48a0568-920c-499a-adc8-a566b834f6c8
-- title:
--   Lemma B.1, p. 28 — maximum of N sums of k independent relatively stable variables
-- statement:
--   Let $k\ge1$ and, for each $j\le k$, let $(Y_i^{(j)},i\ge1)$ be a sequence of i.i.d. continuous random variables with infinite right endpoint, all the $Y_i^{(j)}$ (over $i$ and $j$) being independent. Suppose $Y_i^{(j)}$ satisfies Assumption 2.5 with a function $h^{(j)}$:
--   $$
--   \lim_{t\to\infty}\frac{-\log\mathbb P(Y_1^{(j)}>vt)}{-\log\mathbb P(Y_1^{(j)}>t)}=h^{(j)}(v)\qquad(v\in[0,1]).
--   $$
--   Let $a_N^{(j)}$ satisfy $\mathbb P(Y_i^{(j)}\ge a_N^{(j)})=1/N$, and assume relative stability: $\max_{i\le N}Y_i^{(j)}/a_N^{(j)}\to1$ in probability for each $j$. Then
--   $$
--   \max_{i\le N}\sum_{j=1}^{k}\frac{Y_i^{(j)}}{a_N^{(j)}}\ \xrightarrow{\ \mathbb P\ }\ \sup\Big\{\sum_{j=1}^{k}u^{(j)}\ :\ \sum_{j=1}^{k}h^{(j)}(u^{(j)})\le1,\ u^{(j)}\le1\ \forall j\le k\Big\}\quad(N\to\infty).
--   $$
--
--   This extreme-value result for sums of independent coordinates is the engine behind Lemma 4.4: one coordinate is Gaussian, the other is the initial condition.
--
--   **Formalization Note** The sequences are indexed from $0$ and the maximum over $i\le N$ ranges over $N$ indices. The normalising condition $\mathbb P(Y^{(j)}\ge a_N^{(j)})=1/N$ is required for $N\ge2$ only: at $N=1$ it asks for a sure event, which an unbounded-below variable does not provide. The supremum is taken over $0\le u^{(j)}\le1$; the lower bound $0$ is added because $h^{(j)}$ is defined on $[0,1]$ only, and it does not change the supremum ($h^{(j)}(0)=0$ and $h^{(j)}\ge0$). "Continuous" is encoded as "no atoms", and identical distribution as `IdentDistrib` with the first element.
-- source:
--   Schol, Vlasiou & Zwart, Large fork-join queues with nearly deterministic arrival and service times, arXiv:1912.11661v3, p. 28, Appendix B, Lemma B.1

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model

namespace LargeForkJoin.FluidLimit

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_B_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (Yv : Fin k → ℕ → Ω → ℝ) (h : Fin k → ℝ → ℝ) (a : Fin k → ℕ → ℝ)
    (hmeas : ∀ j i, Measurable (Yv j i))
    (hcont : ∀ j, ∀ x : ℝ, P {ω | Yv j 0 ω = x} = 0)
    (hident : ∀ j i, IdentDistrib (Yv j i) (Yv j 0) P P)
    (hindep : iIndepFun (fun p : Fin k × ℕ => Yv p.1 p.2) P)
    (hright : ∀ j, ∀ t : ℝ, 0 < P {ω | t < Yv j 0 ω})
    (hA25 : ∀ j, ∀ v ∈ Set.Icc (0 : ℝ) 1, Tendsto (fun t : ℝ =>
      -Real.log (P {ω | v * t < Yv j 0 ω}).toReal / -Real.log (P {ω | t < Yv j 0 ω}).toReal)
      atTop (𝓝 (h j v)))
    (ha : ∀ j, ∀ N : ℕ, 2 ≤ N → P {ω | a j N ≤ Yv j 0 ω} = (N : ENNReal)⁻¹)
    (hstable : ∀ j, ∀ ε > 0, Tendsto (fun N : ℕ =>
      P {ω | ε < |(⨆ i : Fin N, Yv j i ω / a j N) - 1|}) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun N : ℕ => P {ω | ε <
      |(⨆ i : Fin N, ∑ j, Yv j i ω / a j N) -
        sSup {x : ℝ | ∃ u : Fin k → ℝ, (∀ j, 0 ≤ u j ∧ u j ≤ 1) ∧ ∑ j, h j (u j) ≤ 1 ∧
          x = ∑ j, u j}|}) atTop (𝓝 0) := by sorry
end LargeForkJoin.FluidLimit
