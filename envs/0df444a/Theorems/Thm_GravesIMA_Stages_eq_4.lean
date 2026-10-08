-- Prove2me | Theorems.Thm_GravesIMA_Stages_eq_4
-- name    : GravesIMA.Stages.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:07.171982+00:00
-- url     : https://prove2.me/theorems/30a27234-3fa0-45b2-bf9c-22b2c49e0425
-- title:
--   (4), p. 52 — the forecast error is d_t − F_t = ε_t
-- statement:
--   Throughout, time is indexed by the integers, $0\le\alpha\le1$, and $(d_t, F_t, q_t, x_t)$ is the single-stage system of Graves (1999, §2) driven by a shock sequence $(\varepsilon_t)_{t\ge1}$: demand $d_1=\mu+\varepsilon_1$, $d_t=d_{t-1}-(1-\alpha)\varepsilon_{t-1}+\varepsilon_t$ for $t\ge2$; the exponentially weighted moving-average forecast $F_1=\mu$, $F_{t+1}=\alpha d_t+(1-\alpha)F_t$; orders $q_t=\mu$ for $t\le0$ and $q_t=d_t+L(F_{t+1}-F_t)$ for $t\ge1$ with lead time $L\in\mathbb N$; inventory $x_t=x_{t-1}-d_t+q_{t-L}$ for $t\ge1$, with the initial inventory $x_0$ free.
--
--   Then for every period $t\ge1$ the forecast error is the current shock:
--   $$d_t-F_t=\varepsilon_t .$$
--
--   So the exponentially weighted moving average is an unbiased forecast for this demand process.
--
--   **Formalization Note** The statement is pathwise: it holds for every real shock sequence, so no probability is involved. The system is the predicate `IsStage μ α L ε d F q x` of `GravesIMA.Stages.Model`; all sequences are functions $\mathbb Z\to\mathbb R$. The standing assumption $0\le\alpha\le1$ of §2 is kept as a hypothesis although the identity does not need it.
-- source:
--   Graves, A single-item inventory model for a nonstationary demand process, Manuf. Serv. Oper. Manag. 1(1) (1999), p. 52, (4)

import Mathlib
import Definitions.Def_GravesIMA_Stages_Model

namespace GravesIMA.Stages

theorem eq_4 (μ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (L : ℕ) (ε d F q x : ℤ → ℝ)
    (h : IsStage μ α L ε d F q x) (t : ℤ) (ht : 1 ≤ t) :
    d t - F t = ε t := by sorry

end GravesIMA.Stages
