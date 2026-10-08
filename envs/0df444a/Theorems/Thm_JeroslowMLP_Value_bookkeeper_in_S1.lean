-- Prove2me | Theorems.Thm_JeroslowMLP_Value_bookkeeper_in_S1
-- name    : JeroslowMLP.Value.bookkeeper_in_S1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:15:59.84535+00:00
-- url     : https://prove2.me/theorems/b5a976cf-4d01-4d9f-91d2-e8d94c171502
-- title:
--   §4, pp. 154–155 — in S₁ of J′(F) the bookkeeper sets z = |2y − x| on (4.1) and z = fr(x) = min{x, 1 − x} on (4.6)
-- statement:
--   In the game $J'(F)$, let $x\in S_1$, i.e. a point after the bookkeeper (player $0$) has moved. Then:
--
--   1. every (4.1) gadget on $\xi$ (that is, $\xi=x_{kj}$ or $\xi=1-x_{kj}$ for an atom of a block $k\ge2$) has $z=|2y-\xi|$;
--   2. every (4.6) gadget on an atom $x_{1j}$ of block $1$ has $z=\min\{x_{1j},1-x_{1j}\}=fr(x_{1j})$;
--   3. the (4.6) gadget on $x(F)$ has $z=\min\{x(F),1-x(F)\}=fr(x(F))$.
--
--   These identities turn the linear criteria of players $1,\dots,p$ into the piecewise-linear functions $Z_k$ of (4.4)–(4.8).
--
--   **Formalization Note** Lean's block `k : Fin p` is the paper's $X_{k+1}$; `gArg x g s` is $\xi$.
-- source:
--   Jeroslow, The polynomial hierarchy and a simple model for competitive analysis, Math. Programming 32 (1985), p. 154 (after (4.1)) and p. 155 (after (4.6))

import Mathlib
import Definitions.Def_JeroslowMLP_Value_Game

namespace JeroslowMLP.Value

open MultilevelProgram GVar

theorem bookkeeper_in_S1 (p : ℕ) (n : Fin p → ℕ) (F : Formula (Atom p n))
    (x : GVar p n F → ℝ) (hx : x ∈ (jGame p n F).solSet 1) :
    (∀ g s, x (gz g s) = |2 * x (gy g s) - gArg x g s|) ∧
    (∀ a, x (fz a) = min (x (atom a.1)) (1 - x (atom a.1))) ∧
    x fzF = min (xF x) (1 - xF x) := by sorry

end JeroslowMLP.Value
