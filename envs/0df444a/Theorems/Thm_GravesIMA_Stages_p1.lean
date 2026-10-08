-- Prove2me | Theorems.Thm_GravesIMA_Stages_p1
-- name    : GravesIMA.Stages.p1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:58.920957+00:00
-- url     : https://prove2.me/theorems/39326d57-0f03-43ea-8b6f-c3cf2529b891
-- title:
--   P1, p. 53 — x_t = x_0 − Σ_{i=0}^{L−1} ε_{t−i}(1 + iα), with ε_t = 0 for t ≤ 0
-- statement:
--   Let $(d_t,F_t,q_t,x_t)$ be a single inventory stage of Graves (1999, §2) with mean level $\mu$, a parameter $a\in[0,1]$, lead time $L\in\mathbb N$ and shocks $(e_t)_{t\ge1}$: $d_1=\mu+e_1$, $d_t=d_{t-1}-(1-a)e_{t-1}+e_t$ for $t\ge2$; $F_1=\mu$, $F_{t+1}=a d_t+(1-a)F_t$; $q_t=\mu$ for $t\le0$, $q_t=d_t+L(F_{t+1}-F_t)$ for $t\ge1$; $x_t=x_{t-1}-d_t+q_{t-L}$ for $t\ge1$. Extend the shocks by $e_t=0$ for $t\le0$.
--
--   **Property P1.** For every period $t\ge1$,
--   $$x_t=x_0-\sum_{i=0}^{L-1}e_{t-i}\,(1+i a).$$
--
--   The inventory is the initial inventory minus a fixed linear combination of the last $L$ shocks; this is what makes its distribution explicit. The statement is for any parameter and any shock sequence, so that it can be applied to the upstream stage in the proof of P2 (with parameter $\beta$ and shocks $\zeta_t=(1+L\alpha)\varepsilon_t$).
--
--   **Formalization Note** The statement is pathwise and holds for every real shock sequence. The convention $e_t=0$ for $t\le0$ is implemented by the masked sequence `masked e`, not by a hypothesis; the model never reads $e_t$ for $t\le0$. It covers $1\le t<L$ as well, as the paper states.
-- source:
--   Graves, A single-item inventory model for a nonstationary demand process, Manuf. Serv. Oper. Manag. 1(1) (1999), p. 53, P1

import Mathlib
import Definitions.Def_GravesIMA_Stages_Model

namespace GravesIMA.Stages

theorem p1 (μ a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (L : ℕ) (e d F q x : ℤ → ℝ)
    (h : IsStage μ a L e d F q x) (t : ℤ) (ht : 1 ≤ t) :
    x t = x 0 - ∑ i ∈ Finset.range L, masked e (t - (i : ℤ)) * (1 + (i : ℝ) * a) := by sorry

end GravesIMA.Stages
