-- Prove2me | Theorems.Thm_GravesIMA_Stages_eq_10
-- name    : GravesIMA.Stages.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:58.329119+00:00
-- url     : https://prove2.me/theorems/063dd120-8de5-44bc-a6d8-11d93fba3e72
-- title:
--   (10), p. 55 — q_1 = μ + ζ_1, q_{t+1} = q_t − (1 − β)ζ_t + ζ_{t+1}, with ζ_t = (1+Lα)ε_t, β = α/(1+Lα), and 0 ≤ β ≤ α
-- statement:
--   Throughout, time is indexed by the integers, $0\le\alpha\le1$, and $(d_t, F_t, q_t, x_t)$ is the single-stage system of Graves (1999, §2) driven by a shock sequence $(\varepsilon_t)_{t\ge1}$: demand $d_1=\mu+\varepsilon_1$, $d_t=d_{t-1}-(1-\alpha)\varepsilon_{t-1}+\varepsilon_t$ for $t\ge2$; the exponentially weighted moving-average forecast $F_1=\mu$, $F_{t+1}=\alpha d_t+(1-\alpha)F_t$; orders $q_t=\mu$ for $t\le0$ and $q_t=d_t+L(F_{t+1}-F_t)$ for $t\ge1$ with lead time $L\in\mathbb N$; inventory $x_t=x_{t-1}-d_t+q_{t-L}$ for $t\ge1$, with the initial inventory $x_0$ free. Put $\zeta_t=(1+L\alpha)\varepsilon_t$ and $\beta=\alpha/(1+L\alpha)$.
--
--   Then the order stream is again an integrated moving average process of order $(0,1,1)$, with shocks $\zeta_t$ and parameter $\beta$:
--   $$q_1=\mu+\zeta_1,\qquad q_{t+1}=q_t-(1-\beta)\zeta_t+\zeta_{t+1}\quad(t\ge1),$$
--   and moreover $0\le\beta\le\alpha$ (the paper: "$0\le\beta\le\alpha\le1$", p. 55).
--
--   This identifies the demand process of the upstream stage: it has the same form as the downstream demand (1), with larger shocks and more inertia.
--
--   **Formalization Note** The statement is pathwise: it holds for every real shock sequence, so no probability is involved. The system is the predicate `IsStage μ α L ε d F q x` of `GravesIMA.Stages.Model`; all sequences are functions $\mathbb Z\to\mathbb R$. The standing assumption $0\le\alpha\le1$ of §2 is kept as a hypothesis although the identity does not need it.
-- source:
--   Graves, A single-item inventory model for a nonstationary demand process, Manuf. Serv. Oper. Manag. 1(1) (1999), p. 55, (10) and the sentence after it

import Mathlib
import Definitions.Def_GravesIMA_Stages_Model

namespace GravesIMA.Stages

theorem eq_10 (μ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (L : ℕ) (ε d F q x : ℤ → ℝ)
    (h : IsStage μ α L ε d F q x) :
    q 1 = μ + (1 + (L : ℝ) * α) * ε 1 ∧
      (∀ t : ℤ, 1 ≤ t → q (t + 1) =
        q t - (1 - upBeta α L) * ((1 + (L : ℝ) * α) * ε t) + (1 + (L : ℝ) * α) * ε (t + 1)) ∧
      0 ≤ upBeta α L ∧ upBeta α L ≤ α := by sorry

end GravesIMA.Stages
