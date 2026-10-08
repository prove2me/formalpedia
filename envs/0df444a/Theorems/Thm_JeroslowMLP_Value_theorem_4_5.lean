-- Prove2me | Theorems.Thm_JeroslowMLP_Value_theorem_4_5
-- name    : JeroslowMLP.Value.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:16:19.552403+00:00
-- url     : https://prove2.me/theorems/be0c3d88-54c3-4738-9e96-68d28853b8bf
-- title:
--   Theorem 4.5, p. 159 — for p ≥ 2, J′(F) has optima, all binary; x(F) = 1 iff (3.3) holds; value 2n_p + 1 − x(F)
-- statement:
--   Let $p\ge2$, let $F$ be a propositional formula over blocks $X_1,\dots,X_p$ of sizes $n_1,\dots,n_p$, and let $S=S_{p+1}$ be the set of optimal solutions of the $(p+1)$-level game $J'(F)$. Then:
--
--   1. $S\neq\emptyset$;
--   2. at every $x\in S$ all atom variables and all $x(G)$ are binary;
--   3. at every $x\in S$, $x(F)=1$ if and only if the $\Sigma_p$ sentence (3.3) $(\exists X_p)(\forall X_{p-1})\cdots(Q_1X_1)[F=1]$ is true;
--   4. the value of $J'(F)$ (player $p$'s criterion on $S$) is
--   $$Z_p=2n_p+1-x(F)=\begin{cases}2n_p,&\text{(3.3) true},\\2n_p+1,&\text{(3.3) false};\end{cases}$$
--   5. if (3.3) is true, a vector $v\in\mathbb R^{n_p}$ is player $p$'s block in some optimal solution if and only if $v$ is binary and
--   $$(Q_{p-1}X_{p-1})\cdots(Q_1X_1)\,[F(X_1,\dots,X_{p-1},\alpha)=1] \qquad (4.17)$$
--   holds, where $\alpha$ is the truth valuation of $v$.
--
--   The paper states this as: "the $(p+1)$ level game $J'(F)$ has a binary value, and this value is zero iff $F\in B_p$. Furthermore, all optimal solutions are binary vectors." The theorem reduces truth of $\Sigma_p$ sentences to the value of a linear multi-level program with fixed criteria, so computing such values is $\Sigma_p$-hard.
--
--   **Formalization Note** The paper's "binary value, zero iff $F\in B_p$" describes the explicit term $1-x(F)$ of $Z_p=1-x(F)+2\sum_jP(x_{pj})$; the term $2\sum_j P(x_{pj})=2n_p$ is the same constant in every optimum (the proof of Lemma 4.4 computes $Z_k=2n_k$ or $1+2n_k$). Items 3 and 4 state the value exactly. "All optimal solutions are binary vectors" is read as the atom variables and the $x(G)$: the gadget variable $z$ of (4.1) equals $2$ at $y=1,\xi=0$. Item 5 is the theorem's last sentence ("the additional fact emerged in the proof of Lemma 4.4"). Player $p$ is index `p` of the game and its block is `⟨p - 1, _⟩`.
-- source:
--   Jeroslow, The polynomial hierarchy and a simple model for competitive analysis, Math. Programming 32 (1985), p. 159, Theorem 4.5, (4.17)

import Mathlib
import Definitions.Def_JeroslowMLP_Value_Game

namespace JeroslowMLP.Value

open MultilevelProgram GVar

theorem theorem_4_5 (p : ℕ) (hp : 2 ≤ p) (n : Fin p → ℕ) (F : Formula (Atom p n)) :
    let S := (jGame p n F).solSet (p + 1)
    let top : Fin p := ⟨p - 1, by omega⟩
    S.Nonempty ∧
    (∀ x ∈ S, (∀ a, IsBinary (x (atom a))) ∧ (∀ g, IsBinary (x (node g)))) ∧
    (∀ x ∈ S, (xF x = 1 ↔ Sentence33 p n F)) ∧
    (Sentence33 p n F → (jGame p n F).HasValue (p + 1) (2 * (n top : ℝ))) ∧
    (¬ Sentence33 p n F → (jGame p n F).HasValue (p + 1) (2 * (n top : ℝ) + 1)) ∧
    (Sentence33 p n F → ∀ w : Fin (n top) → ℝ,
      ((∃ x ∈ S, ∀ j, x (atom ⟨top, j⟩) = w j) ↔
        ((∀ j, IsBinary (w j)) ∧
          QHolds p n F (p - 1) (fun a => if h : a.1 = top then
            decide (w (Fin.cast (by rw [h]) a.2) = 1) else false)))) := by sorry

end JeroslowMLP.Value
