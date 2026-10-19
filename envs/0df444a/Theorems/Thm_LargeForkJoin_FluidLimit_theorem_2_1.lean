-- Prove2me | Theorems.Thm_LargeForkJoin_FluidLimit_theorem_2_1
-- name    : LargeForkJoin.FluidLimit.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:13.272112+00:00
-- url     : https://prove2.me/theorems/0da467e3-eeee-480e-aafb-6028a6e43227
-- title:
--   Theorem 2.1, p. 8 — fluid limit: sup_{t≤T} |Q(tN³log N)/(N log N) − q(t)| → 0 in probability
-- statement:
--   **Fluid limit of the maximum queue length with a non-zero initial condition.**
--
--   Consider $N$ parallel servers in discrete time. In each slot one task arrives with probability $p^{(N)}=1-\alpha/N-\beta/N^2$ and is sent to every server (fork); independently, each server completes a task with probability $q^{(N)}=1-\alpha/N$, where $\alpha,\beta>0$. Server $i$ starts with $Q_i^{(N)}(0)=\lfloor r_NU_i\rfloor$ tasks, where $U_1,U_2,\dots$ are i.i.d., the initial queue lengths are non-negative, and $r_N\ge0$. Let $Q^{(N)}_{(\alpha,\beta)}(n)$ be the largest of the $N$ queue lengths at time $n$, given by Lindley's recursion (2.3). Assume that $Q^{(N)}_{(\alpha,\beta)}(0)/(N\log N)\to q(0)\ge0$ in probability (Assumption 2.3) and that either $U_1$ has a finite right endpoint (Assumption 2.4), or $U_1$ is continuous with $-\log\mathbb P(U_1>vt)/-\log\mathbb P(U_1>t)\to h(v)$ as $t\to\infty$ for all $v\in[0,1]$ (Assumption 2.5). Then for every $T>0$ and every $\epsilon>0$
--   $$
--   \mathbb P\left(\sup_{0\le t\le T}\left|\frac{Q^{(N)}_{(\alpha,\beta)}(tN^3\log N)}{N\log N}-q(t)\right|>\epsilon\right)\xrightarrow{N\to\infty}0,
--   $$
--   with
--   $$
--   q(t)=\max\left(\big(\sqrt{2\alpha t}-\beta t\big)\mathbb 1\Big(t<\frac{\alpha}{2\beta^2}\Big)+\frac{\alpha}{2\beta}\mathbb 1\Big(t\ge\frac{\alpha}{2\beta^2}\Big),\ g(t,q(0))-\beta t\right),
--   $$
--   where
--   1. under Assumption 2.4, $g(t,q(0))=q(0)+\sqrt{2\alpha t}$;
--   2. under Assumption 2.5, $g(t,q(0))=\sup\{\sqrt{2\alpha t}\,u+q(0)v : u^2+h(v)\le1,\ 0\le u\le1,\ 0\le v\le1\}$.
--
--   The maximum queue length is the bottleneck of a fork-join system (a product is complete only when all its parts are). The theorem says that on the time scale $N^3\log N$ and space scale $N\log N$ it follows a deterministic curve: the maximum of the empty-start fluid limit and a term driven by the extreme values of the initial condition.
--
--   **Formalization Note** The two cases of $g$ are two conjuncts. The event "$\sup_{0\le t\le T}|\cdot|>\epsilon$" is written as "there is $t\in[0,T]$ with $|\cdot|>\epsilon$", the same set. Convergence in probability to a constant $c$ is written as $\mathbb P(|Z_N-c|>\epsilon)\to0$ for every $\epsilon>0$. Times are natural numbers; $Q(tN^3\log N)$ is evaluated at $\lfloor tN^3\log N\rfloor$, which is the paper's convention $Q(n)=Q(\lfloor n\rfloor)$ (p. 25). The model hypothesis bundles Assumption 2.1 ($\alpha,\beta>0$), the Bernoulli laws of Definitions 2.1–2.2, Assumption 2.2 and measurability. Three conventions are added and disclosed: the Bernoulli laws are imposed only for $N\ge N_0$ (for small $N$ the number $p^{(N)}$ may be negative); within each $N\ge N_0$ the arrival indicators, the service indicators and the initial-condition variables $U_i$ are mutually independent (the paper never states that $(U_i)$ is independent of arrivals and services, but its proofs use it); servers are indexed $0,\dots,N-1$ instead of $1,\dots,N$. Assumption 2.5 includes the added condition $\mathbb P(U_1>t)>0$ for every $t$ (infinite right endpoint), without which the ratio in Assumption 2.5 is undefined.
-- source:
--   Schol, Vlasiou & Zwart, Large fork-join queues with nearly deterministic arrival and service times, arXiv:1912.11661v3, p. 8, Theorem 2.1 (2.4)–(2.7)

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model

namespace LargeForkJoin.FluidLimit

open MeasureTheory ProbabilityTheory Filter Topology

theorem theorem_2_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ForkJoin Ω) (α β qInit : ℝ) (N₀ : ℕ)
    (hM : IsModel P M α β N₀) (h23 : Assumption23 P M qInit) :
    (Assumption24 P M → ∀ T > 0, ∀ ε > 0,
        Tendsto (fun N : ℕ => P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T,
          ε < |maxQueue M N (tau N t) ω / scale N - fluid α β (gFinite α qInit) t|}) atTop (𝓝 0)) ∧
    (∀ h : ℝ → ℝ, Assumption25 P M h → ∀ T > 0, ∀ ε > 0,
        Tendsto (fun N : ℕ => P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T,
          ε < |maxQueue M N (tau N t) ω / scale N - fluid α β (gGumbel α h qInit) t|}) atTop (𝓝 0)) := by sorry
end LargeForkJoin.FluidLimit
