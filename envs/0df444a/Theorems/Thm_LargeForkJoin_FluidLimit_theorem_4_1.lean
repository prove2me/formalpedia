-- Prove2me | Theorems.Thm_LargeForkJoin_FluidLimit_theorem_4_1
-- name    : LargeForkJoin.FluidLimit.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:06.214343+00:00
-- url     : https://prove2.me/theorems/5e0b6fd8-76d7-45de-babd-27c1ca3a39de
-- title:
--   Theorem 4.1, p. 18 — pointwise convergence of the scaled maximum queue length to q(t)
-- statement:
--   In the fork-join model with initial queue lengths $Q_i^{(N)}(0)=\lfloor r_NU_i\rfloor$ satisfying Assumption 2.3 with limit $q(0)$, and under Assumption 2.4 or Assumption 2.5, for every $t>0$,
--   $$
--   \frac{Q^{(N)}_{(\alpha,\beta)}(tN^3\log N)}{N\log N}\ \xrightarrow{\ \mathbb P\ }\ q(t)\qquad(N\to\infty),
--   $$
--   with $q(t)=\max\big((\sqrt{2\alpha t}-\beta t)\mathbb 1(t<\frac{\alpha}{2\beta^2})+\frac{\alpha}{2\beta}\mathbb 1(t\ge\frac{\alpha}{2\beta^2}),\ g(t,q(0))-\beta t\big)$ as in (2.5), where $g(t,q(0))=q(0)+\sqrt{2\alpha t}$ under Assumption 2.4 and $g(t,q(0))=\sup\{\sqrt{2\alpha t}\,u+q(0)v: u^2+h(v)\le1,\ 0\le u,v\le1\}$ under Assumption 2.5.
--
--   This is the pointwise (fixed-time) version of the main result, Theorem 2.1.
--
--   **Formalization Note** The two cases of $g$ are two conjuncts. $Q^{(N)}_{(\alpha,\beta)}$ is the maximum queue length (2.3) built from the Bernoulli indicators. Convergence in probability to a constant $c$ is written as $\mathbb P(|Z_N-c|>\epsilon)\to0$ for every $\epsilon>0$. Times are natural numbers; $Q(tN^3\log N)$ is evaluated at $\lfloor tN^3\log N\rfloor$, which is the paper's convention $Q(n)=Q(\lfloor n\rfloor)$ (p. 25). The model hypothesis bundles Assumption 2.1 ($\alpha,\beta>0$), the Bernoulli laws of Definitions 2.1–2.2, Assumption 2.2 and measurability. Three conventions are added and disclosed: the Bernoulli laws are imposed only for $N\ge N_0$ (for small $N$ the number $p^{(N)}$ may be negative); within each $N\ge N_0$ the arrival indicators, the service indicators and the initial-condition variables $U_i$ are mutually independent (the paper never states that $(U_i)$ is independent of arrivals and services, but its proofs use it); servers are indexed $0,\dots,N-1$ instead of $1,\dots,N$.
-- source:
--   Schol, Vlasiou & Zwart, Large fork-join queues with nearly deterministic arrival and service times, arXiv:1912.11661v3, p. 18, Theorem 4.1 (4.10); p. 8, (2.5)–(2.7)

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model

namespace LargeForkJoin.FluidLimit

open MeasureTheory ProbabilityTheory Filter Topology

theorem theorem_4_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ForkJoin Ω) (α β qInit : ℝ) (N₀ : ℕ)
    (hM : IsModel P M α β N₀) (h23 : Assumption23 P M qInit) (t : ℝ) (ht : 0 < t) :
    (Assumption24 P M → ∀ ε > 0, Tendsto (fun N : ℕ => P {ω | ε <
      |maxQueue M N (tau N t) ω / scale N - fluid α β (gFinite α qInit) t|}) atTop (𝓝 0)) ∧
    (∀ h : ℝ → ℝ, Assumption25 P M h → ∀ ε > 0, Tendsto (fun N : ℕ => P {ω | ε <
      |maxQueue M N (tau N t) ω / scale N - fluid α β (gGumbel α h qInit) t|}) atTop (𝓝 0)) := by sorry
end LargeForkJoin.FluidLimit
