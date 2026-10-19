-- Prove2me | Theorems.Thm_LargeForkJoin_FluidLimit_corollary_4_1
-- name    : LargeForkJoin.FluidLimit.corollary_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:04.440821+00:00
-- url     : https://prove2.me/theorems/a240211c-1b89-499f-9c5a-1b87d5e05366
-- title:
--   Corollary 4.1, p. 27 — tightness of the scaled maximum queue-length process on [0, T]
-- statement:
--   In the fork-join model with initial queue lengths $Q_i^{(N)}(0)=\lfloor r_NU_i\rfloor$ satisfying Assumption 2.3, fix $T>0$ and write $X^{(N)}(t)=Q^{(N)}_{(\alpha,\beta)}(tN^3\log N)/(N\log N)$ for the scaled maximum queue length (2.3). The process $(X^{(N)}(t),t\in[0,T])$ is tight, in the sense of the two conditions (4.21)–(4.22) of p. 25:
--
--   1. for every $\eta>0$ there are $a$ and $N_0'$ with $\mathbb P(|X^{(N)}(0)|>a)\le\eta$ for all $N\ge N_0'$;
--   2. for every $\epsilon>0$ and $\eta>0$ there are $0<\delta<1$ and $N_0'$ such that for all $N\ge N_0'$ and all $t\in[0,T]$
--   $$
--   \frac1\delta\,\mathbb P\Big(\sup_{t\le s\le t+\delta}\big|X^{(N)}(s)-X^{(N)}(t)\big|>\epsilon\Big)\le\eta .
--   $$
--
--   Together with the pointwise limit (Theorem 4.1), tightness upgrades the convergence to uniform convergence on $[0,T]$ (Theorem 2.1).
--
--   **Formalization Note** "Tight" is stated as the two conditions the paper proves, (4.21) and (4.22) of p. 25, with (4.22) required for every $t\in[0,T]$ as in Lemmas 4.11–4.12; this is the criterion of Billingsley's Theorem 7.3 that the paper cites. The supremum event is written as "there is $s\in[t,t+\delta]$ with $|\cdot|>\epsilon$". The model hypothesis bundles Assumption 2.1 ($\alpha,\beta>0$), the Bernoulli laws of Definitions 2.1–2.2, Assumption 2.2 and measurability. Three conventions are added and disclosed: the Bernoulli laws are imposed only for $N\ge N_0$ (for small $N$ the number $p^{(N)}$ may be negative); within each $N\ge N_0$ the arrival indicators, the service indicators and the initial-condition variables $U_i$ are mutually independent (the paper never states that $(U_i)$ is independent of arrivals and services, but its proofs use it); servers are indexed $0,\dots,N-1$ instead of $1,\dots,N$.
-- source:
--   Schol, Vlasiou & Zwart, Large fork-join queues with nearly deterministic arrival and service times, arXiv:1912.11661v3, p. 27, Corollary 4.1; p. 25, (4.21)–(4.22)

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model

namespace LargeForkJoin.FluidLimit

open MeasureTheory ProbabilityTheory Filter Topology

theorem corollary_4_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ForkJoin Ω) (α β qInit : ℝ) (N₀ : ℕ)
    (hM : IsModel P M α β N₀) (h23 : Assumption23 P M qInit) (T : ℝ) (hT : 0 < T) :
    (∀ η > 0, ∃ a : ℝ, ∃ N₁ : ℕ, ∀ N ≥ N₁,
      (P {ω | a < |maxQueue M N (tau N 0) ω / scale N|}).toReal ≤ η) ∧
    (∀ ε > 0, ∀ η > 0, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ t ∈ Set.Icc (0 : ℝ) T,
      1 / δ * (P {ω | ∃ s ∈ Set.Icc t (t + δ), ε <
        |maxQueue M N (tau N s) ω / scale N - maxQueue M N (tau N t) ω / scale N|}).toReal
        ≤ η) := by sorry
end LargeForkJoin.FluidLimit
