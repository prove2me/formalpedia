-- Prove2me | Theorems.Thm_MetricalTaskSystem_Deterministic_astar_f_sub_le
-- name    : MetricalTaskSystem.Deterministic.astar_f_sub_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:13:47.090994+00:00
-- url     : https://prove2.me/theorems/ea05c00c-f7b8-4363-9381-154d865a6101
-- title:
--   Lemma 6.3 — $f_k(s)-f_k(s')\le d(s',s)$
-- statement:
--   Let $(S,d)$ be a task system with at least two states, $s_0\in S$, and let $s_0,s_1,s_2,\dots$ be the state sequence and $f_0,f_1,\dots$ the functions of the algorithm $A^*_d$. Then for every $k\ge0$,
--   $$f_k(s)-f_k(s')\le d(s',s)\qquad\text{for all }s,s'\in S .$$
--
--   It is one of the three lemmas from which the competitive bound of $A^*_d$ (Theorem 6.1) is deduced.
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), p. 756, Lemma 6.3

import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_AstarD

namespace MetricalTaskSystem.Deterministic

/-- **Lemma 6.3** (Borodin–Linial–Saks 1992, p. 756). For the functions `f_k` of the algorithm
`A*_d`: `f_k(x) − f_k(y) ≤ d(y, x)` for all states `x, y` and all `k ≥ 0`. -/
theorem astar_f_sub_le {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (s₀ : S) (s : ℕ → S) (hs : IsAstarSeq d s₀ s)
    (k : ℕ) (x y : S) :
    fSeq d s k x - fSeq d s k y ≤ d y x := by sorry

end MetricalTaskSystem.Deterministic
