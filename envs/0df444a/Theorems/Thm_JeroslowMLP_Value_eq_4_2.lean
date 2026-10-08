-- Prove2me | Theorems.Thm_JeroslowMLP_Value_eq_4_2
-- name    : JeroslowMLP.Value.eq_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:16:10.194746+00:00
-- url     : https://prove2.me/theorems/e6c1c169-4e5c-4980-92c2-593221c9ad1f
-- title:
--   (4.2), §4, p. 154 — in S₂ of J′(F), y = 1 if 0 ≤ x < 1, and y ∈ {0, 1} if x = 1
-- statement:
--   In the game $J'(F)$, let $x\in S_2$ (after the bookkeeper and player $1$ have moved). For every (4.1) gadget with argument $\xi$ and variable $y$,
--   $$0\le\xi<1\ \Rightarrow\ y=1,\qquad \xi=1\ \Rightarrow\ y\in\{0,1\}. \qquad (4.2)$$
--
--   Player 1 chooses $y$ to maximise $z=|2y-\xi|$; (4.2) records the maximisers.
--
--   **Formalization Note** The statement holds for every $p$; for $p\le1$ there are no (4.1) gadgets.
-- source:
--   Jeroslow, The polynomial hierarchy and a simple model for competitive analysis, Math. Programming 32 (1985), p. 154, §4, (4.2)

import Mathlib
import Definitions.Def_JeroslowMLP_Value_Game

namespace JeroslowMLP.Value

open MultilevelProgram GVar

theorem eq_4_2 (p : ℕ) (n : Fin p → ℕ) (F : Formula (Atom p n))
    (x : GVar p n F → ℝ) (hx : x ∈ (jGame p n F).solSet 2)
    (g : {a : Atom p n // 1 ≤ a.1.val}) (s : Bool) :
    (0 ≤ gArg x g s ∧ gArg x g s < 1 → x (gy g s) = 1) ∧
    (gArg x g s = 1 → x (gy g s) = 0 ∨ x (gy g s) = 1) := by sorry

end JeroslowMLP.Value
