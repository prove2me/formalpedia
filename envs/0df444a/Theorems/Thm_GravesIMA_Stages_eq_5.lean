-- Prove2me | Theorems.Thm_GravesIMA_Stages_eq_5
-- name    : GravesIMA.Stages.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:56.698886+00:00
-- url     : https://prove2.me/theorems/e50c27ac-2f18-4f97-b33d-59064a0f0f6e
-- title:
--   (5), p. 52 — F_{t+1} = F_t + αε_t = αε_t + ⋯ + αε_1 + μ
-- statement:
--   Throughout, time is indexed by the integers, $0\le\alpha\le1$, and $(d_t, F_t, q_t, x_t)$ is the single-stage system of Graves (1999, §2) driven by a shock sequence $(\varepsilon_t)_{t\ge1}$: demand $d_1=\mu+\varepsilon_1$, $d_t=d_{t-1}-(1-\alpha)\varepsilon_{t-1}+\varepsilon_t$ for $t\ge2$; the exponentially weighted moving-average forecast $F_1=\mu$, $F_{t+1}=\alpha d_t+(1-\alpha)F_t$; orders $q_t=\mu$ for $t\le0$ and $q_t=d_t+L(F_{t+1}-F_t)$ for $t\ge1$ with lead time $L\in\mathbb N$; inventory $x_t=x_{t-1}-d_t+q_{t-L}$ for $t\ge1$, with the initial inventory $x_0$ free.
--
--   Then for every period $t\ge1$ the forecast updates by a fixed fraction of the shock, and in closed form:
--   $$F_{t+1}=F_t+\alpha\varepsilon_t,\qquad F_{t+1}=\alpha\sum_{j=1}^{t}\varepsilon_j+\mu .$$
--
--   Both identities are used repeatedly to express orders and inventories through the shocks.
--
--   **Formalization Note** The statement is pathwise: it holds for every real shock sequence, so no probability is involved. The system is the predicate `IsStage μ α L ε d F q x` of `GravesIMA.Stages.Model`; all sequences are functions $\mathbb Z\to\mathbb R$. The standing assumption $0\le\alpha\le1$ of §2 is kept as a hypothesis although the identity does not need it.
-- source:
--   Graves, A single-item inventory model for a nonstationary demand process, Manuf. Serv. Oper. Manag. 1(1) (1999), p. 52, (5)

import Mathlib
import Definitions.Def_GravesIMA_Stages_Model

namespace GravesIMA.Stages

theorem eq_5 (μ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (L : ℕ) (ε d F q x : ℤ → ℝ)
    (h : IsStage μ α L ε d F q x) (t : ℤ) (ht : 1 ≤ t) :
    F (t + 1) = F t + α * ε t ∧
      F (t + 1) = α * ∑ j ∈ Finset.Icc (1 : ℤ) t, ε j + μ := by sorry

end GravesIMA.Stages
