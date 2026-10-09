-- Prove2me | Theorems.Thm_ModernOnlineLearning_ParameterFree_eq_13_1
-- name    : ModernOnlineLearning.ParameterFree.eq_13_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:39:35.684434+00:00
-- url     : https://prove2.me/theorems/02d4613a-63bd-4e09-9259-be7839f4f39f
-- title:
--   Display (13.1), p. 210 — KT potential one-step inequality
-- statement:
--   Let $F_t$ be the KT gamma-function potential with initial wealth $\varepsilon>0$. For an integer $t\ge1$, a coin value $c\in[-1,1]$, and a previous cumulative outcome $z\in[-(t-1),t-1]$,
--   $$F_t(z+c)\le\left(1+\frac{cz}{t}\right)F_{t-1}(z).$$
--
--   This inequality makes the potential compatible with the bettor's wealth update for continuous coin outcomes.
-- source:
--   Orabona, arXiv:1912.13213v10, display (13.1), p. 210

import Mathlib
import Definitions.Def_ModernOnlineLearning_ParameterFree_Defs

namespace ModernOnlineLearning.ParameterFree

/-- Display (13.1), p. 210: one step of the KT gamma-function potential. -/
theorem eq_13_1 (ε : ℝ) (hε : 0 < ε) (t : ℕ) (ht : 1 ≤ t)
    (c z : ℝ) (hc : -1 ≤ c ∧ c ≤ 1)
    (hz : -((t - 1 : ℕ) : ℝ) ≤ z ∧ z ≤ ((t - 1 : ℕ) : ℝ)) :
    ktPotential ε t (z + c) ≤
      (1 + c * z / (t : ℝ)) * ktPotential ε (t - 1) z := by sorry

end ModernOnlineLearning.ParameterFree
