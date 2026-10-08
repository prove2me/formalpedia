-- Prove2me | Theorems.Thm_JeroslowMLP_Value_eq_4_3
-- name    : JeroslowMLP.Value.eq_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:16:10.207249+00:00
-- url     : https://prove2.me/theorems/6033bc9f-cd07-4d79-a4c2-38c7af36679a
-- title:
--   (4.3), §4, p. 154 — at the level of player k ≥ 2, y = p(x) with p(x) = 1 on [0,1) and p(1) = 0
-- statement:
--   In the game $J'(F)$, let $k\ge2$ be a player, $x_{kj}$ one of its atoms, and $x\in S_{k+1}$ (the set after player $k$ has moved). For both gadgets of $x_{kj}$ (on $\xi=x_{kj}$ and on $\xi=1-x_{kj}$) the variable $y$ equals
--   $$p(\xi)=\begin{cases}1,&0\le\xi<1,\\0,&\xi=1,\end{cases}\qquad (4.3)$$
--   and consequently
--   $$y_{x_{kj}}+y_{1-x_{kj}}=P(x_{kj})=p(x_{kj})+p(1-x_{kj})=\begin{cases}1,&x_{kj}\in\{0,1\},\\2,&0<x_{kj}<1.\end{cases}$$
--
--   The term $2P(x_{kj})$ in player $k$'s criterion therefore penalises fractional choices.
--
--   **Formalization Note** Lean block `k : Fin p` with `1 ≤ k.val` is the paper's block and player $k+1\ge2$, whose level is `k.val + 2`; since atoms lie in $[0,1]$, $p(\xi)$ is written `if ξ < 1 then 1 else 0`.
-- source:
--   Jeroslow, The polynomial hierarchy and a simple model for competitive analysis, Math. Programming 32 (1985), p. 154, §4, (4.3), and P(x) = p(x) + p(1 − x), Fig. 1b, pp. 154–155

import Mathlib
import Definitions.Def_JeroslowMLP_Value_Game

namespace JeroslowMLP.Value

open MultilevelProgram GVar

theorem eq_4_3 (p : ℕ) (n : Fin p → ℕ) (F : Formula (Atom p n)) (k : Fin p) (hk : 1 ≤ k.val)
    (x : GVar p n F → ℝ) (hx : x ∈ (jGame p n F).solSet (k.val + 2)) (j : Fin (n k)) :
    (∀ s : Bool, x (gy ⟨⟨k, j⟩, hk⟩ s) = if gArg x ⟨⟨k, j⟩, hk⟩ s < 1 then 1 else 0) ∧
    x (gy ⟨⟨k, j⟩, hk⟩ false) + x (gy ⟨⟨k, j⟩, hk⟩ true) =
      if x (atom ⟨k, j⟩) = 0 ∨ x (atom ⟨k, j⟩) = 1 then 1 else 2 := by sorry

end JeroslowMLP.Value
