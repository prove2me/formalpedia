-- Prove2me | Theorems.Thm_FrieszDUE_FIFO_intervals_cover_Rplus
-- name    : FrieszDUE.FIFO.intervals_cover_Rplus
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:21:03.226992+00:00
-- url     : https://prove2.me/theorems/b7f043bf-0056-41a9-a8a8-319ed11979f5
-- title:
--   Proof of Theorem 1, p. 186 — t_{n+1} − t_n ≥ β and ℝ₊ = ⋃_{n≥0} [t_n, t_{n+1}]
-- statement:
--   Let $\alpha, \beta > 0$, let the entry rate $u$ be nonnegative and continuous on $[0, \infty)$, and let $\tau$ be an exit-time function for the linear delay $D = \alpha x + \beta$, i.e. $\tau(t) = t + \alpha x(t) + \beta$ for all $t \ge 0$, where $x(t)$ is the mass of the vehicles that entered during $[0,t]$ and have not exited by time $t$. Let $t_0 = 0$ and $t_{n+1} = \tau(t_n)$. Then
--
--   1. consecutive partition times are at least $\beta$ apart:
--   $$t_{n+1} - t_n \ge \beta \quad \text{for all } n \ge 0;$$
--   2. the intervals $[t_n, t_{n+1}]$ cover the nonnegative half-line:
--   $$\mathbb R_+ = \bigcup_{n \ge 0}\, [t_n, t_{n+1}] .$$
--
--   This is the closing step of the proof of Theorem 1: monotonicity established on each interval $[t_n, t_{n+1}]$ then holds on all of $\mathbb R_+$.
--
--   **Formalization Note** The nonnegativity and continuity of $u$ on $[0,\infty)$ are the standing hypotheses of the mission (an entry rate is nonnegative; the remark after Theorem 1 covers "all continuous entry rate patterns").
-- source:
--   Friesz, Bernstein, Smith, Tobin and Wie, A variational inequality formulation of the dynamic network user equilibrium problem, Oper. Res. 41 (1993), p. 186, proof of Theorem 1, closing paragraph

import Mathlib
import Definitions.Def_FrieszDUE_FIFO_Setting

namespace FrieszDUE.FIFO

theorem intervals_cover_Rplus (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (u : ℝ → ℝ)
    (hu_nonneg : ∀ t, 0 ≤ t → 0 ≤ u t) (hu_cont : ContinuousOn u (Set.Ici 0))
    (τ : ℝ → ℝ) (hτ : IsLinearExitTime α β u τ) :
    (∀ n : ℕ, β ≤ tSeq τ (n + 1) - tSeq τ n) ∧
      (⋃ n : ℕ, Set.Icc (tSeq τ n) (tSeq τ (n + 1))) = Set.Ici 0 := by sorry

end FrieszDUE.FIFO
