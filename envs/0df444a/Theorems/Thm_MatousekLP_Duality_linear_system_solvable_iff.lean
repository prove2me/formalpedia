-- Prove2me | Theorems.Thm_MatousekLP_Duality_linear_system_solvable_iff
-- name    : MatousekLP.Duality.linear_system_solvable_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T11:04:40.030564+00:00
-- url     : https://prove2.me/theorems/43d8fcef-819d-4d1e-aa96-550f210edab1
-- title:
--   Lemma 6.6.2 — solvability of Ax = b
-- statement:
--   Let $A$ be a real $m\times n$ matrix and $b\in\mathbb{R}^m$. The system $Ax=b$ has a solution $x\in\mathbb{R}^n$ if and only if every $y\in\mathbb{R}^m$ with $y^{T}A=0^{T}$ also satisfies
--
--   $$y^{T}b=0.$$
--
--   This is the linear-algebra counterpart of the Farkas lemma (the entry "$Ax=b$ has a solution $x\in\mathbb{R}^n$" of the book's table of variants); it is used in §6.6 to derive the Farkas lemma from minimally infeasible systems.
--
--   **Formalization Note** $y^{T}A=0^{T}$ is written `Aᵀ *ᵥ y = 0` and $y^{T}b$ is `y ⬝ᵥ b`.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 99, Lemma 6.6.2

import Mathlib

namespace MatousekLP.Duality

open Matrix

/-- Matoušek & Gärtner, Lemma 6.6.2 (p. 99): the system `Ax = b` has a solution if and only if
every `y ∈ ℝ^m` with `yᵀA = 0ᵀ` (written `Aᵀ *ᵥ y = 0`) also satisfies `yᵀb = 0`. -/
theorem linear_system_solvable_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, A *ᵥ x = b) ↔ ∀ y : Fin m → ℝ, Aᵀ *ᵥ y = 0 → y ⬝ᵥ b = 0 := by sorry

end MatousekLP.Duality
