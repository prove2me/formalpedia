-- Prove2me | Theorems.Thm_GravesIMA_Stages_upstream_forecast_eq
-- name    : GravesIMA.Stages.upstream_forecast_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:56.902279+00:00
-- url     : https://prove2.me/theorems/a3f62090-acfa-462d-85a7-fdc5316b9d3b
-- title:
--   §3, p. 55 — q_t = G_t + ζ_t, q_t = F_t + (1+Lα)ε_t, hence G_t = F_t
-- statement:
--   Throughout, time is indexed by the integers, $0\le\alpha\le1$, and $(d_t, F_t, q_t, x_t)$ is the single-stage system of Graves (1999, §2) driven by a shock sequence $(\varepsilon_t)_{t\ge1}$: demand $d_1=\mu+\varepsilon_1$, $d_t=d_{t-1}-(1-\alpha)\varepsilon_{t-1}+\varepsilon_t$ for $t\ge2$; the exponentially weighted moving-average forecast $F_1=\mu$, $F_{t+1}=\alpha d_t+(1-\alpha)F_t$; orders $q_t=\mu$ for $t\le0$ and $q_t=d_t+L(F_{t+1}-F_t)$ for $t\ge1$ with lead time $L\in\mathbb N$; inventory $x_t=x_{t-1}-d_t+q_{t-L}$ for $t\ge1$, with the initial inventory $x_0$ free. The two-stage system of §3 adds an upstream stage with lead time $K\in\mathbb N$ that sees the orders $q_t$ as its demand: forecast $G_1=\mu$, $G_{t+1}=\beta q_t+(1-\beta)G_t$ with $\beta=\alpha/(1+L\alpha)$; orders $p_t=\mu$ for $t\le0$ and $p_t=q_t+K(G_{t+1}-G_t)$ for $t\ge1$; inventory $y_t=y_{t-1}-q_t+p_{t-K}$ for $t\ge1$, with $y_0$ free.
--
--   Then for every period $t\ge1$,
--   $$q_t=G_t+(1+L\alpha)\varepsilon_t,\qquad q_t=F_t+(1+L\alpha)\varepsilon_t,\qquad G_t=F_t .$$
--
--   The upstream forecast coincides with the downstream forecast, and its error on the upstream demand is the shock $\zeta_t=(1+L\alpha)\varepsilon_t$. Together with (10), this shows that the upstream stage is itself a single stage of the form of §2, with parameter $\beta$, lead time $K$ and shocks $\zeta_t$, which is how property P1 is applied to it in the proof of P2.
--
--   **Formalization Note** The statement is pathwise and holds for every real shock sequence; the two-stage system is the predicate `IsTwoStage`. The standing assumption $0\le\alpha\le1$ is kept as a hypothesis; $\alpha\ge0$ guarantees $1+L\alpha\neq0$.
-- source:
--   Graves, A single-item inventory model for a nonstationary demand process, Manuf. Serv. Oper. Manag. 1(1) (1999), p. 55, §3, Order Amplification, the two unnumbered displays after (11)

import Mathlib
import Definitions.Def_GravesIMA_Stages_Model

namespace GravesIMA.Stages

theorem upstream_forecast_eq (μ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (L K : ℕ)
    (ε d F q x G p y : ℤ → ℝ) (h : IsTwoStage μ α L K ε d F q x G p y) (t : ℤ) (ht : 1 ≤ t) :
    q t = G t + (1 + (L : ℝ) * α) * ε t ∧ q t = F t + (1 + (L : ℝ) * α) * ε t ∧ G t = F t := by sorry

end GravesIMA.Stages
