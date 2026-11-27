-- Prove2me | Theorems.Thm_LefebvreVariations_motzkin_transposition_dim_one
-- name    : LefebvreVariations.motzkin_transposition_dim_one
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:17:50.646055+00:00
-- url     : https://prove2.me/theorems/961198ba-72fb-52a5-8241-3cada9183fd1
-- title:
--   Lefebvre's variations, No. 247 — on a theme by Mangasarian: Motzkin's transposition theorem on the line
-- statement:
--   Let $a\ge 1$ and $b,c\ge 0$ be integers, and let $A_1,\dots,A_a$, $B_1,\dots,B_b$, $C_1,\dots,C_c$ be real numbers. Then exactly one of the following two systems is solvable:
--   $$
--   \text{(I)}\quad \exists\,y\in\mathbb R:\ yA_i<0\ (\forall i),\quad yB_i\le 0\ (\forall i),\quad yC_i=0\ (\forall i);
--   $$
--   $$
--   \text{(II)}\quad \exists\,z_1\in\mathbb R^a_{\ge0}\setminus\{0\},\ z_2\in\mathbb R^b_{\ge0},\ z_3\in\mathbb R^c:\quad \sum_i z_{1,i}A_i+\sum_i z_{2,i}B_i+\sum_i z_{3,i}C_i=0 .
--   $$
--
--   This is the case of the line ($n=1$) of Motzkin's transposition theorem, which the platform lists as open in every dimension $n$ (there the $A_i,B_i,C_i$ are vectors of $\mathbb R^n$ and $y$ ranges over $\mathbb R^n$). In dimension one every vector is a number, and the two alternatives can be read off the signs of the $A_i,B_i,C_i$.
--
--   **Formalization Note** The line is `EuclideanSpace ℝ (Fin 1)`, with inner product `inner ℝ y (A i)`; the three families are `Fin a`, `Fin b`, `Fin c` indexed with `0 < a`. "Exactly one" is `Xor`; the vector $z_1$ is required to be nonzero as a function `Fin a → ℝ`, and $z_3$ is unrestricted in sign.
--
--   **Why this is a variation.** A variation on the open platform problem MangasarianFJ.GenFJ.motzkin_transposition (Motzkin's transposition theorem in every dimension n), played at n = 1 with the parent's statement restated verbatim at EuclideanSpace ℝ (Fin 1), not imported. The dimension-one case is the first size at which the three families A, B, C interact; the general statement stays open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   T. S. Motzkin, Beiträge zur Theorie der linearen Ungleichungen, doctoral thesis, Basel 1936 (cited from memory); the form with the three families A, B, C is the one used in O. L. Mangasarian, Nonlinear Programming (1969), Chapter 2 (cited from memory; page not verified). The statement here is the one-dimensional instance of the platform's formalization; it is elementary (a case analysis on the signs of the real numbers).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- The one-dimensional case `n = 1` of `MangasarianFJ.GenFJ.motzkin_transposition` (Motzkin's transposition
theorem): for finite families `A`, `B`, `C` of vectors of the line `ℝ¹` (with `A` nonempty), exactly one of the two
systems `y·A_i < 0, y·B_i ≤ 0, y·C_i = 0` (in `y`) and `Σ z₁ᵢ A_i + Σ z₂ᵢ B_i + Σ z₃ᵢ C_i = 0, z₁ ≥ 0, z₁ ≠ 0, z₂ ≥ 0`
(in `z`) is solvable.
Source: T. S. Motzkin, *Beiträge zur Theorie der linearen Ungleichungen*, thesis, Basel 1936; as used in Mangasarian,
*Nonlinear Programming* (1969), Chapter 2 (cited from memory). In dimension one the statement is elementary. -/
theorem motzkin_transposition_dim_one {a b c : ℕ} (ha : 0 < a)
    (A : Fin a → EuclideanSpace ℝ (Fin 1)) (B : Fin b → EuclideanSpace ℝ (Fin 1))
    (C : Fin c → EuclideanSpace ℝ (Fin 1)) :
    Xor
      (∃ y : EuclideanSpace ℝ (Fin 1),
        (∀ i, inner ℝ y (A i) < 0) ∧ (∀ i, inner ℝ y (B i) ≤ 0) ∧ ∀ i, inner ℝ y (C i) = 0)
      (∃ (z₁ : Fin a → ℝ) (z₂ : Fin b → ℝ) (z₃ : Fin c → ℝ),
        ∑ i, z₁ i • A i + ∑ i, z₂ i • B i + ∑ i, z₃ i • C i = 0 ∧
        (∀ i, 0 ≤ z₁ i) ∧ z₁ ≠ 0 ∧ ∀ i, 0 ≤ z₂ i) := by
  sorry

end LefebvreVariations
