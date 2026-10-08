-- Prove2me | Theorems.Thm_GravesIMA_Stages_p1_lead_time_form
-- name    : GravesIMA.Stages.p1_lead_time_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:50.219005+00:00
-- url     : https://prove2.me/theorems/6c1549ab-52bb-430e-ba48-45fc5c2ba411
-- title:
--   Proof of P1, p. 53, first display — x_t = x_0 − Σ_{j=t+1−L}^{t} d_j + LF_{t+1−L}
-- statement:
--   Throughout, time is indexed by the integers, $0\le\alpha\le1$, and $(d_t, F_t, q_t, x_t)$ is the single-stage system of Graves (1999, §2) driven by a shock sequence $(\varepsilon_t)_{t\ge1}$: demand $d_1=\mu+\varepsilon_1$, $d_t=d_{t-1}-(1-\alpha)\varepsilon_{t-1}+\varepsilon_t$ for $t\ge2$; the exponentially weighted moving-average forecast $F_1=\mu$, $F_{t+1}=\alpha d_t+(1-\alpha)F_t$; orders $q_t=\mu$ for $t\le0$ and $q_t=d_t+L(F_{t+1}-F_t)$ for $t\ge1$ with lead time $L\in\mathbb N$; inventory $x_t=x_{t-1}-d_t+q_{t-L}$ for $t\ge1$, with the initial inventory $x_0$ free.
--
--   Then for every period $t$ with $t\ge1$ and $t\ge L$,
--   $$x_t=x_0-\sum_{j=t+1-L}^{t}d_j+L\,F_{t+1-L}=x_0-\sum_{j=t+1-L}^{t}\bigl(d_j-F_{t+1-L}\bigr).$$
--
--   The inventory equals the initial inventory minus the demand over the last $L$ periods, corrected by the forecast of lead-time demand made $L$ periods ago. It is the first step of the proof of property P1.
--
--   **Formalization Note** The statement is pathwise: it holds for every real shock sequence, so no probability is involved. The system is the predicate `IsStage μ α L ε d F q x` of `GravesIMA.Stages.Model`; all sequences are functions $\mathbb Z\to\mathbb R$. The standing assumption $0\le\alpha\le1$ of §2 is kept as a hypothesis although the identity does not need it. The paper writes "for $t\ge L$"; the hypothesis $t\ge1$ is kept as well because periods start at $1$ (it only matters when $L=0$, where the sums are empty and the claim is $x_t=x_0$).
-- source:
--   Graves, A single-item inventory model for a nonstationary demand process, Manuf. Serv. Oper. Manag. 1(1) (1999), p. 53, §2, proof of P1, first display

import Mathlib
import Definitions.Def_GravesIMA_Stages_Model

namespace GravesIMA.Stages

theorem p1_lead_time_form (μ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (L : ℕ)
    (ε d F q x : ℤ → ℝ) (h : IsStage μ α L ε d F q x) (t : ℤ) (ht1 : 1 ≤ t) (htL : (L : ℤ) ≤ t) :
    x t = x 0 - ∑ j ∈ Finset.Icc (t + 1 - (L : ℤ)) t, d j + (L : ℝ) * F (t + 1 - (L : ℤ)) ∧
      x t = x 0 - ∑ j ∈ Finset.Icc (t + 1 - (L : ℤ)) t, (d j - F (t + 1 - (L : ℤ))) := by sorry

end GravesIMA.Stages
