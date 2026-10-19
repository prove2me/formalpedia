-- Prove2me | Theorems.Thm_LargeForkJoin_FluidLimit_lemma_4_4
-- name    : LargeForkJoin.FluidLimit.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:08.090478+00:00
-- url     : https://prove2.me/theorems/c530df8b-bff2-43a9-81fa-2be88af476c0
-- title:
--   Lemma 4.4, p. 17 — pointwise convergence of the Gaussian approximation of the starting position
-- statement:
--   In the fork-join model, let $X_1,\dots,X_N$ be i.i.d. standard normal variables, independent of the initial queue lengths $Q_i^{(N)}(0)=\lfloor r_NU_i\rfloor$. Suppose Assumption 2.3 holds with limit $q(0)$, and fix $t>0$. Then
--   $$
--   \max_{i\le N}\left(\frac{\sqrt{\alpha t}\,X_i}{\sqrt{\log N}}+\frac{Q_i^{(N)}(0)}{N\log N}\right)\ \xrightarrow{\ \mathbb P\ }\ g(t,q(0))\qquad(N\to\infty),
--   $$
--   where $g(t,q(0))=q(0)+\sqrt{2\alpha t}$ if Assumption 2.4 holds and $g(t,q(0))=\sup\{\sqrt{2\alpha t}\,u+q(0)v: u^2+h(v)\le1,\ 0\le u,v\le1\}$ if Assumption 2.5 holds with function $h$.
--
--   The lemma identifies the contribution of the initial condition to the fluid limit $q(t)$ in a Gaussian surrogate; Lemma 4.9 transfers it to the queue.
--
--   **Formalization Note** The Gaussian variables are not part of the queueing model, so the statement is about the law of the pairs $(X_i,U_i)_{i\le N}$: the product of $N$ copies of (standard normal) $\otimes$ (law of $U_1$). The two cases of $g$ are two conjuncts. The paper's lemma carries no restriction on $t$; it is used for $t>0$ (Theorem 4.1), which is the range stated. The model hypothesis bundles Assumption 2.1 ($\alpha,\beta>0$), the Bernoulli laws of Definitions 2.1–2.2, Assumption 2.2 and measurability. Three conventions are added and disclosed: the Bernoulli laws are imposed only for $N\ge N_0$ (for small $N$ the number $p^{(N)}$ may be negative); within each $N\ge N_0$ the arrival indicators, the service indicators and the initial-condition variables $U_i$ are mutually independent (the paper never states that $(U_i)$ is independent of arrivals and services, but its proofs use it); servers are indexed $0,\dots,N-1$ instead of $1,\dots,N$.
-- source:
--   Schol, Vlasiou & Zwart, Large fork-join queues with nearly deterministic arrival and service times, arXiv:1912.11661v3, p. 17, Lemma 4.4; p. 8, Theorem 2.1 (2.6)–(2.7)

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model

namespace LargeForkJoin.FluidLimit

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_4_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ForkJoin Ω) (α β qInit : ℝ) (N₀ : ℕ)
    (hM : IsModel P M α β N₀) (h23 : Assumption23 P M qInit) (t : ℝ) (ht : 0 < t) :
    (Assumption24 P M → ∀ ε > 0, Tendsto (fun N : ℕ =>
      gaussPairLaw P M N {w | ε < |gaussPairMax M α N t w - gFinite α qInit t|}) atTop (𝓝 0)) ∧
    (∀ h : ℝ → ℝ, Assumption25 P M h → ∀ ε > 0, Tendsto (fun N : ℕ =>
      gaussPairLaw P M N {w | ε < |gaussPairMax M α N t w - gGumbel α h qInit t|}) atTop (𝓝 0)) := by sorry
end LargeForkJoin.FluidLimit
