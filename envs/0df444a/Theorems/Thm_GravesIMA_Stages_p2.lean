-- Prove2me | Theorems.Thm_GravesIMA_Stages_p2
-- name    : GravesIMA.Stages.p2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:55.545066+00:00
-- url     : https://prove2.me/theorems/f07039fa-a951-4fb0-8851-3f4cc618deb4
-- title:
--   P2, p. 57 — y_t = y_0 − Σ_{i=0}^{K−1} ε_{t−i}(1 + (L + i)α), with ε_t = 0 for t ≤ 0
-- statement:
--   Throughout, time is indexed by the integers, $0\le\alpha\le1$, and $(d_t, F_t, q_t, x_t)$ is the single-stage system of Graves (1999, §2) driven by a shock sequence $(\varepsilon_t)_{t\ge1}$: demand $d_1=\mu+\varepsilon_1$, $d_t=d_{t-1}-(1-\alpha)\varepsilon_{t-1}+\varepsilon_t$ for $t\ge2$; the exponentially weighted moving-average forecast $F_1=\mu$, $F_{t+1}=\alpha d_t+(1-\alpha)F_t$; orders $q_t=\mu$ for $t\le0$ and $q_t=d_t+L(F_{t+1}-F_t)$ for $t\ge1$ with lead time $L\in\mathbb N$; inventory $x_t=x_{t-1}-d_t+q_{t-L}$ for $t\ge1$, with the initial inventory $x_0$ free. The two-stage system of §3 adds an upstream stage with lead time $K\in\mathbb N$ that sees the orders $q_t$ as its demand: forecast $G_1=\mu$, $G_{t+1}=\beta q_t+(1-\beta)G_t$ with $\beta=\alpha/(1+L\alpha)$; orders $p_t=\mu$ for $t\le0$ and $p_t=q_t+K(G_{t+1}-G_t)$ for $t\ge1$; inventory $y_t=y_{t-1}-q_t+p_{t-K}$ for $t\ge1$, with $y_0$ free. Extend the shocks by $\varepsilon_t=0$ for $t\le0$.
--
--   **Property P2.** For every period $t\ge1$,
--   $$y_t=y_0-\sum_{i=0}^{K-1}\varepsilon_{t-i}\,\bigl(1+(L+i)\alpha\bigr).$$
--
--   The upstream inventory is a fixed linear combination of the last $K$ exogenous shocks, with weights that grow with the downstream lead time $L$.
--
--   **Formalization Note** The statement is pathwise; the convention $\varepsilon_t=0$ for $t\le0$ is implemented by `masked ε`, not by a hypothesis. The standing assumption $0\le\alpha\le1$ is kept.
-- source:
--   Graves, A single-item inventory model for a nonstationary demand process, Manuf. Serv. Oper. Manag. 1(1) (1999), p. 57, P2

import Mathlib
import Definitions.Def_GravesIMA_Stages_Model

namespace GravesIMA.Stages

theorem p2 (μ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (L K : ℕ) (ε d F q x G p y : ℤ → ℝ)
    (h : IsTwoStage μ α L K ε d F q x G p y) (t : ℤ) (ht : 1 ≤ t) :
    y t = y 0 - ∑ i ∈ Finset.range K, masked ε (t - (i : ℤ)) * (1 + ((L : ℝ) + i) * α) := by sorry

end GravesIMA.Stages
