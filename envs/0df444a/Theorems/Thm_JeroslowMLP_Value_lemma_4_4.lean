-- Prove2me | Theorems.Thm_JeroslowMLP_Value_lemma_4_4
-- name    : JeroslowMLP.Value.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:16:25.353314+00:00
-- url     : https://prove2.me/theorems/b4e74ad4-b117-4efe-a091-941140106d03
-- title:
--   Lemma 4.4, p. 158 — with X_{k+1},…,X_p fixed to binary v, J′(F) has optima; all have x, x(F) binary, x(F) = 1 iff (4.15)
-- statement:
--   Let $p\ge k\ge1$ and let $v^{k+1},\dots,v^p$ be binary vectors for the blocks $X_{k+1},\dots,X_p$, with truth values $\alpha^{k+1},\dots,\alpha^p$. Let $J'(F)(v^{k+1},\dots,v^p)$ be the game obtained from $J'(F)$ by fixing $x^t=v^t$ for $k+1\le t\le p$, played by $0,1,\dots,k$ with the criteria of $J'(F)$. Then this game has an optimal solution, and every optimal solution has all atom variables and all $x(G)$ binary, with
--   $$x(F)=1\iff (Q_kX_k)\cdots(Q_1X_1)\,[F(X_1,\dots,X_k,\alpha^{k+1},\dots,\alpha^p)=1]. \qquad (4.15)$$
--   In particular $x(F)$ is the same in all optimal solutions.
--
--   This is the inductive core of the reduction: each level of the game evaluates one quantifier.
--
--   **Formalization Note** The subgame's optimal solutions are the points of the full game's level set $S_{k+1}$ whose blocks $X_{k+1},\dots,X_p$ equal $v$ (true $\mapsto1$): levels $1,\dots,k+1$ only compare points that agree on those blocks, so the two sets coincide and no separate subgame is built. `v` assigns every atom, but only blocks $X_{k+1},\dots,X_p$ (0-based blocks $\ge k$) are used. "$x$ binary" is read as the atom variables; the $x(G)$ are included because the paper's proof derives it (Lemma 3.1) and Theorem 4.5 claims all optimal solutions binary.
-- source:
--   Jeroslow, The polynomial hierarchy and a simple model for competitive analysis, Math. Programming 32 (1985), p. 158, Lemma 4.4, (4.15)

import Mathlib
import Definitions.Def_JeroslowMLP_Value_Game

namespace JeroslowMLP.Value

open MultilevelProgram GVar

theorem lemma_4_4 (p : ℕ) (n : Fin p → ℕ) (F : Formula (Atom p n)) (k : ℕ)
    (hk1 : 1 ≤ k) (hkp : k ≤ p) (v : Atom p n → Bool) :
    let Slice : Set (GVar p n F → ℝ) :=
      {x | x ∈ (jGame p n F).solSet (k + 1) ∧
        ∀ a : Atom p n, k ≤ a.1.val → x (atom a) = if v a then 1 else 0}
    Slice.Nonempty ∧
    ∀ x ∈ Slice, (∀ a, IsBinary (x (atom a))) ∧ (∀ g, IsBinary (x (node g))) ∧
      (xF x = 1 ↔ QHolds p n F k v) := by sorry

end JeroslowMLP.Value
