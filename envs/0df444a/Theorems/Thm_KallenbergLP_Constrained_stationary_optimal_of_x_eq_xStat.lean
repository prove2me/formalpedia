-- Prove2me | Theorems.Thm_KallenbergLP_Constrained_stationary_optimal_of_x_eq_xStat
-- name    : KallenbergLP.Constrained.stationary_optimal_of_x_eq_xStat
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:39.328483+00:00
-- url     : https://prove2.me/theorems/51eea07f-57ce-41c3-8f00-e45714b6f896
-- title:
--   Theorem 4.7.4 — if x* = x(π*), the stationary policy (π*)^∞ is optimal for the constrained problem
-- statement:
--   Let $(x^*,y^*)$ be an optimal solution of the linear program (4.7.12) (the same program as (4.7.6)) and let $\pi^*$ be a stationary decision rule defined from it by (4.7.14):
--
--   $$\pi^*_{ia}=\begin{cases}x^*_{ia}/\sum_ax^*_{ia}, & i\in E_{x^*},\\ y^*_{ia}/\sum_ay^*_{ia}, & i\in E_{y^*}\setminus E_{x^*},\\ \text{arbitrary}, & \text{elsewhere.}\end{cases}$$
--
--   If $x^*=x(\pi^*)$, where $x_{ja}(\pi)=[\beta^TP^*(\pi)]_j\pi_{ja}$, then the stationary policy $(\pi^*)^\infty$ is an optimal solution of the constrained problem (4.7.5).
--
--   This gives a checkable condition under which the constrained problem has a stationary optimal policy, read directly from the linear program.
--
--   **Formalization Note** $(\pi^*)^\infty$ is `StatRule.toPolicy π hπ`; the arbitrary values of (4.7.14) are left free, subject to $\pi^*$ being a decision rule.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 144, (4.7.14); p. 145, Theorem 4.7.4

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_KallenbergLP_Constrained_Frequencies
import Definitions.Def_KallenbergLP_Constrained_Problem

namespace KallenbergLP.Constrained

open MarkovDecisionProcesses

/-- Kallenberg (1983), Theorem 4.7.4, p. 145: let `(x*, y*)` be an optimal solution of (4.7.12)
(= (4.7.6)) and `π*` a stationary decision rule given by (4.7.14). If `x* = x(π*)`, then
`(π*)^∞` is an optimal solution of problem (4.7.5). -/
theorem stationary_optimal_of_x_eq_xStat {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (M : StationaryMDP S A) (β : S → ℝ) (hβ0 : ∀ j, 0 ≤ β j)
    (hβ1 : ∑ j, β j = 1) {m : ℕ} (q : KallenbergLP.AverageLP.Pair M → Fin m → ℝ) (b : Fin m → ℝ)
    (x y : KallenbergLP.AverageLP.Pair M → ℝ) (hopt : Optimal476 M β q b x y)
    (π : KallenbergLP.AverageLP.Pair M → ℝ) (hπ : π ∈ StatRule M) (h4714 : IsRule4714 x y π)
    (hx : x = xStat β π) :
    Optimal475 β q b (StatRule.toPolicy π hπ) := by sorry

end KallenbergLP.Constrained
