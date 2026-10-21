-- Prove2me | Theorems.Thm_LargeForkJoin_FluidLimit_lemma_4_10
-- name    : LargeForkJoin.FluidLimit.lemma_4_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:15.665687+00:00
-- url     : https://prove2.me/theorems/182fd7f0-ad9c-4890-a747-5e9fe512b333
-- title:
--   Lemma 4.10, p. 25 — u.o.c. convergence is preserved by the pointwise maximum
-- statement:
--   Let $X^{(N)}(s)$ and $Y^{(N)}(s)$, $s\in[0,t]$, be random processes on a probability space and let $k,l:[0,t]\to\mathbb R$ be functions. If $X^{(N)}\to k$ and $Y^{(N)}\to l$ uniformly on $[0,t]$ in probability, i.e.
--   $$
--   \mathbb P\Big(\sup_{0\le s\le t}|X^{(N)}(s)-k(s)|>\epsilon\Big)\to0\quad\text{and}\quad\mathbb P\Big(\sup_{0\le s\le t}|Y^{(N)}(s)-l(s)|>\epsilon\Big)\to0\quad\text{for every }\epsilon>0,
--   $$
--   then $\max(X^{(N)}(s),Y^{(N)}(s))\to\max(k(s),l(s))$ uniformly on $[0,t]$ in probability.
--
--   The maximum queue length (2.3) is the maximum of the empty-start part and the initial-condition part; this lemma lets the two be treated separately.
--
--   **Formalization Note** "u.o.c." (uniformly on compacts) on $[0,t]$ is read, as in the paper's proof, as convergence in probability of the supremum over $[0,t]$. The event "$\sup_{0\le s\le t}|\cdot|>\epsilon$" is written as "there is $s\in[0,t]$ with $|\cdot|>\epsilon$", which is the same set and needs no real supremum.
-- source:
--   Schol, Vlasiou & Zwart, Large fork-join queues with nearly deterministic arrival and service times, arXiv:1912.11661v3, p. 25, Lemma 4.10

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model

namespace LargeForkJoin.FluidLimit

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_4_10 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xp Yp : ℕ → ℝ → Ω → ℝ) (k l : ℝ → ℝ) (t : ℝ)
    (hX : ∀ ε > 0, Tendsto (fun N : ℕ => P {ω | ∃ s ∈ Set.Icc (0 : ℝ) t,
      ε < |Xp N s ω - k s|}) atTop (𝓝 0))
    (hY : ∀ ε > 0, Tendsto (fun N : ℕ => P {ω | ∃ s ∈ Set.Icc (0 : ℝ) t,
      ε < |Yp N s ω - l s|}) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun N : ℕ => P {ω | ∃ s ∈ Set.Icc (0 : ℝ) t,
      ε < |max (Xp N s ω) (Yp N s ω) - max (k s) (l s)|}) atTop (𝓝 0) := by sorry
end LargeForkJoin.FluidLimit
