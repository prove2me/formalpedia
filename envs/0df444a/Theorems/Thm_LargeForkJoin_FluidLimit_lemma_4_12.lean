-- Prove2me | Theorems.Thm_LargeForkJoin_FluidLimit_lemma_4_12
-- name    : LargeForkJoin.FluidLimit.lemma_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:13.120983+00:00
-- url     : https://prove2.me/theorems/2bafecf3-0adc-42e1-ad15-0c2685ecc82a
-- title:
--   Lemma 4.12, p. 26 — tightness of the starting-position part and boundedness of Q(0)/(N log N)
-- statement:
--   In the fork-join model with initial queue lengths $Q_i^{(N)}(0)=\lfloor r_NU_i\rfloor$ satisfying Assumption 2.3, write
--   $$
--   Z^{(N)}(s)=\max_{i\le N}\frac{A^{(N)}(sN^3\log N)-S_i^{(N)}(sN^3\log N)+Q_i^{(N)}(0)}{N\log N}.
--   $$
--   1. For every $\epsilon>0$, $\eta>0$ and $T>0$ there exist $0<\delta<1$ and an integer $N_0'$ such that for all $N\ge N_0'$ and $t\in[0,T]$
--   $$
--   \frac1\delta\,\mathbb P\Big(\sup_{t\le s\le t+\delta}\big|Z^{(N)}(s)-Z^{(N)}(t)\big|>\epsilon\Big)<\eta. \tag{4.30}
--   $$
--   2. For every $\eta>0$ there is $a>0$ with
--   $$
--   \mathbb P\left(\frac{Q^{(N)}_{(\alpha,\beta)}(0)}{N\log N}>a\right)<\eta. \tag{4.31}
--   $$
--
--   These are the two tightness conditions (4.21)–(4.22) for the initial-condition part of the maximum queue length.
--
--   **Formalization Note** The supremum event is written as "there is $s\in[t,t+\delta]$ with $|\cdot|>\epsilon$" (the same set). The page does not quantify $N$ in (4.31); the Lean statement asks for one $a$ that works for every $N$ (each scaled maximum is a finite random variable, and Assumption 2.3 handles large $N$). The paper's $N_0$ is called $N_1$. Assumptions 2.4/2.5 are not needed and not assumed. The model hypothesis bundles Assumption 2.1 ($\alpha,\beta>0$), the Bernoulli laws of Definitions 2.1–2.2, Assumption 2.2 and measurability. Three conventions are added and disclosed: the Bernoulli laws are imposed only for $N\ge N_0$ (for small $N$ the number $p^{(N)}$ may be negative); within each $N\ge N_0$ the arrival indicators, the service indicators and the initial-condition variables $U_i$ are mutually independent (the paper never states that $(U_i)$ is independent of arrivals and services, but its proofs use it); servers are indexed $0,\dots,N-1$ instead of $1,\dots,N$.
-- source:
--   Schol, Vlasiou & Zwart, Large fork-join queues with nearly deterministic arrival and service times, arXiv:1912.11661v3, p. 26, Lemma 4.12 (4.30)–(4.31)

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model

namespace LargeForkJoin.FluidLimit

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_4_12 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ForkJoin Ω) (α β qInit : ℝ) (N₀ : ℕ)
    (hM : IsModel P M α β N₀) (h23 : Assumption23 P M qInit) :
    (∀ ε > 0, ∀ η > 0, ∀ T > 0, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ N₁ : ℕ, ∀ N ≥ N₁,
      ∀ t ∈ Set.Icc (0 : ℝ) T,
      1 / δ * (P {ω | ∃ s ∈ Set.Icc t (t + δ), ε <
        |maxStartPart M N (tau N s) ω / scale N - maxStartPart M N (tau N t) ω / scale N|}).toReal
        < η) ∧
    (∀ η > 0, ∃ a > 0, ∀ N : ℕ, (P {ω | a < maxInit M N ω / scale N}).toReal < η) := by sorry
end LargeForkJoin.FluidLimit
