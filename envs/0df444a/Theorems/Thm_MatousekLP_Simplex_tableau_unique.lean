-- Prove2me | Theorems.Thm_MatousekLP_Simplex_tableau_unique
-- name    : MatousekLP.Simplex.tableau_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T21:02:46.797978+00:00
-- url     : https://prove2.me/theorems/9b2fbfd2-d11f-47f9-9354-597dda512ff2
-- title:
--   Lemma 5.5.1 — the simplex tableau of a feasible basis exists, is unique, and is given by explicit formulas
-- statement:
--   Let $A$ be a real $m\times n$ matrix of rank $m$ with $n\ge m$, let $b\in\mathbb{R}^m$, $c\in\mathbb{R}^n$, and let $B$ be a feasible basis of the linear program "maximize $c^Tx$ subject to $Ax=b$, $x\ge0$", with complement $N$. Then a quadruple $(p,Q,z_0,r)$ defines a simplex tableau
--   $$x_B=p+Qx_N,\qquad z=z_0+r^Tx_N$$
--   (a system with the same solutions $(x,z)$ as $Ax=b$, $z=c^Tx$) if and only if
--   $$Q=-A_B^{-1}A_N,\qquad p=A_B^{-1}b,\qquad z_0=c_B^TA_B^{-1}b,\qquad r=c_N-(c_B^TA_B^{-1}A_N)^T.$$
--   In particular each feasible basis has exactly one simplex tableau $T(B)$.
--
--   The lemma is what makes "the" tableau of a basis well defined, and it lets every later statement about the simplex method read the tableau's parameters from $A$, $b$, $c$ and $B$ alone.
--
--   **Formalization Note** Indices are 0-based; $x_B$ and $x_N$ list the basic and nonbasic variables in increasing order of index. The standing assumption of §4.2 ($n\ge m$, rank $A=m$) is a hypothesis.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 66, Lemma 5.5.1 (tableau defined on p. 65; standing assumption of §4.2 on p. 44)

import Mathlib
import Definitions.Def_MatousekLP_Simplex_Tableau
open Matrix Filter

namespace MatousekLP.Simplex

/-- Lemma 5.5.1 (p. 66). For a feasible basis `B` there is exactly one simplex tableau, given by
`Q = −A_B⁻¹ A_N`, `p = A_B⁻¹ b`, `z₀ = c_Bᵀ A_B⁻¹ b`, `r = c_N − (c_Bᵀ A_B⁻¹ A_N)ᵀ`.
Standing assumption of §4.2 (p. 44): `n ≥ m` and `A` has rank `m`. -/
theorem tableau_unique {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hmn : m ≤ n) (hrank : A.rank = m) (B : Finset (Fin n)) (hB : B.card = m)
    (hfeas : IsFeasibleBasisOf A b B hB) (p : Fin m → ℝ) (Q : Matrix (Fin m) (Fin (n - m)) ℝ)
    (z₀ : ℝ) (r : Fin (n - m) → ℝ) :
    IsSimplexTableau A b c B hB p Q z₀ r ↔
      (Q = tableauQ A B hB ∧ p = tableauP A b B hB ∧ z₀ = tableauZ0 A b c B hB ∧
        r = tableauR A c B hB) := by sorry

end MatousekLP.Simplex
