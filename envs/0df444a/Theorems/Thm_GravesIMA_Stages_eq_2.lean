-- Prove2me | Theorems.Thm_GravesIMA_Stages_eq_2
-- name    : GravesIMA.Stages.eq_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:49.084409+00:00
-- url     : https://prove2.me/theorems/806be234-2a0e-4f7d-9f85-3c4d2d601b11
-- title:
--   (2), p. 51 — d_t = ε_t + αε_{t−1} + ⋯ + αε_1 + μ
-- statement:
--   Throughout, time is indexed by the integers, $0\le\alpha\le1$, and $(d_t, F_t, q_t, x_t)$ is the single-stage system of Graves (1999, §2) driven by a shock sequence $(\varepsilon_t)_{t\ge1}$: demand $d_1=\mu+\varepsilon_1$, $d_t=d_{t-1}-(1-\alpha)\varepsilon_{t-1}+\varepsilon_t$ for $t\ge2$; the exponentially weighted moving-average forecast $F_1=\mu$, $F_{t+1}=\alpha d_t+(1-\alpha)F_t$; orders $q_t=\mu$ for $t\le0$ and $q_t=d_t+L(F_{t+1}-F_t)$ for $t\ge1$ with lead time $L\in\mathbb N$; inventory $x_t=x_{t-1}-d_t+q_{t-L}$ for $t\ge1$, with the initial inventory $x_0$ free.
--
--   Then for every period $t\ge1$,
--   $$d_t=\varepsilon_t+\alpha\sum_{j=1}^{t-1}\varepsilon_j+\mu .$$
--
--   Each shock has weight one in its own period and a permanent weight $\alpha$ afterwards; this expansion of (1) is the basis for every later closed form.
--
--   **Formalization Note** The statement is pathwise: it holds for every real shock sequence, so no probability is involved. The system is the predicate `IsStage μ α L ε d F q x` of `GravesIMA.Stages.Model`; all sequences are functions $\mathbb Z\to\mathbb R$. The standing assumption $0\le\alpha\le1$ of §2 is kept as a hypothesis although the identity does not need it.
-- source:
--   Graves, A single-item inventory model for a nonstationary demand process, Manuf. Serv. Oper. Manag. 1(1) (1999), p. 51, (2)

import Mathlib
import Definitions.Def_GravesIMA_Stages_Model

namespace GravesIMA.Stages

theorem eq_2 (μ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (L : ℕ) (ε d F q x : ℤ → ℝ)
    (h : IsStage μ α L ε d F q x) (t : ℤ) (ht : 1 ≤ t) :
    d t = ε t + α * ∑ j ∈ Finset.Ico (1 : ℤ) t, ε j + μ := by sorry

end GravesIMA.Stages
