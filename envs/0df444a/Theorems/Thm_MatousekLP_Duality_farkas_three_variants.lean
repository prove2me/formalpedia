-- Prove2me | Theorems.Thm_MatousekLP_Duality_farkas_three_variants
-- name    : MatousekLP.Duality.farkas_three_variants
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T11:04:34.311106+00:00
-- url     : https://prove2.me/theorems/72a763c2-5936-455f-9905-88261ccb70bc
-- title:
--   Proposition 6.4.3 — the Farkas lemma in three variants
-- statement:
--   Let $A$ be a real matrix with $m$ rows and $n$ columns and let $b\in\mathbb{R}^m$. All vector inequalities are componentwise.
--
--   1. The system $Ax=b$ has a solution $x\ge 0$ if and only if every $y\in\mathbb{R}^m$ with $y^{T}A\ge 0^{T}$ also satisfies $y^{T}b\ge 0$.
--   2. The system $Ax\le b$ has a solution $x\ge 0$ if and only if every $y\in\mathbb{R}^m$ with $y\ge 0$ and $y^{T}A\ge 0^{T}$ also satisfies $y^{T}b\ge 0$.
--   3. The system $Ax\le b$ has a solution $x\in\mathbb{R}^n$ if and only if every $y\in\mathbb{R}^m$ with $y\ge 0$ and $y^{T}A=0^{T}$ also satisfies $y^{T}b\ge 0$.
--
--   In each part the condition on the right is a certificate-of-infeasibility test: a vector $y$ violating it combines the constraints into an obviously unsatisfiable inequality. Part (ii) is the form used in the proof of the duality theorem from the Farkas lemma.
--
--   **Formalization Note** The row vector $y^{T}A$ is represented as the column vector $A^{T}y$, so $y^{T}A\ge 0^{T}$ is `0 ≤ Aᵀ *ᵥ y` and $y^{T}A=0^{T}$ is `Aᵀ *ᵥ y = 0`; $y^{T}b$ is the dot product `y ⬝ᵥ b`. The three parts are stated as one conjunction.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, pp. 90–91, Proposition 6.4.3

import Mathlib

namespace MatousekLP.Duality

open Matrix

/-- Matoušek & Gärtner, Proposition 6.4.3 (pp. 90–91), the Farkas lemma in three variants.
`yᵀA ≥ 0ᵀ` is written `0 ≤ Aᵀ *ᵥ y` and `yᵀA = 0ᵀ` is `Aᵀ *ᵥ y = 0`.
(i) `Ax = b` has a nonnegative solution iff every `y` with `yᵀA ≥ 0ᵀ` has `yᵀb ≥ 0`;
(ii) `Ax ≤ b` has a nonnegative solution iff every `y ≥ 0` with `yᵀA ≥ 0ᵀ` has `yᵀb ≥ 0`;
(iii) `Ax ≤ b` has a solution iff every `y ≥ 0` with `yᵀA = 0ᵀ` has `yᵀb ≥ 0`. -/
theorem farkas_three_variants {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    ((∃ x : Fin n → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ↔
        ∀ y : Fin m → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b) ∧
    ((∃ x : Fin n → ℝ, 0 ≤ x ∧ A *ᵥ x ≤ b) ↔
        ∀ y : Fin m → ℝ, 0 ≤ y → 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b) ∧
    ((∃ x : Fin n → ℝ, A *ᵥ x ≤ b) ↔
        ∀ y : Fin m → ℝ, 0 ≤ y → Aᵀ *ᵥ y = 0 → 0 ≤ y ⬝ᵥ b) := by sorry

end MatousekLP.Duality
