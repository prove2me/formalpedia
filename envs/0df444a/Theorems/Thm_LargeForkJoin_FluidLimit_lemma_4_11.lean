-- Prove2me | Theorems.Thm_LargeForkJoin_FluidLimit_lemma_4_11
-- name    : LargeForkJoin.FluidLimit.lemma_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:19.151836+00:00
-- url     : https://prove2.me/theorems/33ee2098-1f74-4a7c-b8cd-a778d079f808
-- title:
--   Lemma 4.11, p. 25 — tightness of the empty-start part
-- statement:
--   In the fork-join model started empty ($Q^{(N)}_{(\alpha,\beta)}(0)=0$), for every $\epsilon>0$, $\eta>0$ and $T>0$ there exist $0<\delta<1$ and an integer $N_0'$ such that for all $N\ge N_0'$ and all $t\in[0,T]$
--   $$
--   \frac1\delta\,\mathbb P\left(\sup_{t\le s\le t+\delta}\left|\frac{Q^{(N)}_{(\alpha,\beta)}(sN^3\log N)}{N\log N}-\frac{Q^{(N)}_{(\alpha,\beta)}(tN^3\log N)}{N\log N}\right|\ge\epsilon\right)\le\eta .
--   $$
--
--   This is the modulus-of-continuity condition (4.22) for the empty-start part of the scaled maximum queue length.
--
--   **Formalization Note** The event "$\sup_{t\le s\le t+\delta}|\cdot|\ge\epsilon$" is written as "there is $s\in[t,t+\delta]$ with $|\cdot|\ge\epsilon$". The two coincide here because the process takes finitely many values on $[t,t+\delta]$ (it is evaluated at the integer times $\lfloor sN^3\log N\rfloor$), so the supremum is attained. The paper's integer $N_0$ is called $N_1$ in Lean, to keep it apart from the threshold $N_0$ of the Bernoulli laws. The model hypothesis bundles Assumption 2.1 ($\alpha,\beta>0$), the Bernoulli laws of Definitions 2.1–2.2, Assumption 2.2 and measurability. Three conventions are added and disclosed: the Bernoulli laws are imposed only for $N\ge N_0$ (for small $N$ the number $p^{(N)}$ may be negative); within each $N\ge N_0$ the arrival indicators, the service indicators and the initial-condition variables $U_i$ are mutually independent (the paper never states that $(U_i)$ is independent of arrivals and services, but its proofs use it); servers are indexed $0,\dots,N-1$ instead of $1,\dots,N$.
-- source:
--   Schol, Vlasiou & Zwart, Large fork-join queues with nearly deterministic arrival and service times, arXiv:1912.11661v3, p. 25, Lemma 4.11 (4.23)

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model

namespace LargeForkJoin.FluidLimit

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_4_11 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ForkJoin Ω) (α β : ℝ) (N₀ : ℕ) (hM : IsModel P M α β N₀) :
    ∀ ε > 0, ∀ η > 0, ∀ T > 0, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ t ∈ Set.Icc (0 : ℝ) T,
      1 / δ * (P {ω | ∃ s ∈ Set.Icc t (t + δ), ε ≤
        |maxQueueEmpty M N (tau N s) ω / scale N - maxQueueEmpty M N (tau N t) ω / scale N|}).toReal
        ≤ η := by sorry
end LargeForkJoin.FluidLimit
