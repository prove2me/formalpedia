-- Prove2me | Theorems.Thm_LogicBenders_Generic_subVal_upper_bound
-- name    : LogicBenders.Generic.subVal_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:33:36.766893+00:00
-- url     : https://prove2.me/theorems/029b4abd-75e3-4b71-8382-99fe729dfd21
-- title:
--   Proof of Theorem 1, p. 9 — the subproblem value at any trial ȳ is an upper bound on the optimal value of (6)
-- statement:
--   Let $S \subseteq D_x \times D_y$ and $f : D_x \times D_y \to \mathbb R$ define problem (6), $\min f(x,y)$ over $(x,y) \in S$. For any trial value $\bar y \in D_y$, the optimal value of the subproblem (7) obtained by fixing $y = \bar y$ is at least the optimal value of (6):
--   $$\inf_{(x,y) \in S} f(x,y) \;\le\; \inf_{x\,:\,(x,\bar y) \in S} f(x,\bar y).$$
--
--   In the proof of Theorem 1 this is the remark that $\beta^*$, the optimal value of the last subproblem, is an upper bound on the optimal value of (6).
--
--   **Formalization Note.** Both values are taken in $[-\infty,+\infty]$; when the subproblem is infeasible its value is $+\infty$ and the inequality is immediate.
-- source:
--   Hooker & Ottosson, Logic-based Benders decomposition, revised manuscript (Nov. 2000), p. 9, proof of Theorem 1, fourth sentence

import Mathlib
import Definitions.Def_LogicBenders_Generic_Setting

namespace LogicBenders.Generic

theorem subVal_upper_bound {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ) (yb : Y) :
    optVal S f ≤ subVal S f yb := by sorry

end LogicBenders.Generic
