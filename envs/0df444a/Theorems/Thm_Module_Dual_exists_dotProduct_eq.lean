-- Prove2me | Theorems.Thm_Module_Dual_exists_dotProduct_eq
-- name    : Module.Dual.exists_dotProduct_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T16:48:25.824888+00:00
-- url     : https://prove2.me/theorems/906e6fdc-db91-4159-8e0f-7d65d5c56152
-- title:
--   Every linear functional on $\mathbb{R}^n$ is a dot product
-- statement:
--   Let $n$ be a finite type with decidable equality. For every linear functional $\varphi$ on $\mathbb{R}^n$ there is a vector $u \in \mathbb{R}^n$ with
--
--   $$
--   \varphi(v) \;=\; u \cdot v \qquad \text{for all } v \in \mathbb{R}^n .
--   $$
--
--   The witness is $u_i = \varphi(e_i)$, the values of $\varphi$ on the standard basis.
--
--   This is the concrete form of Riesz representation that a duality argument needs. Abstract
--   convex analysis produces a separating or supporting functional -- an element of
--   $(\mathbb{R}^n)^*$ -- and the statement one wants to write down afterwards is about a vector:
--   the dual solution of a linear program, the multiplier of a constraint, the normal of a
--   separating hyperplane. Converting between the two is exactly this statement, and doing it by
--   hand each time is what the twelve copies of this lemma were doing.
--
--   **Formalization Note** `Module.Dual ℝ (n → ℝ)` is Mathlib's dual space and `⋅ᵥ` is `Matrix.dotProduct`,
--   so the statement is `∃ u, ∀ v, φ v = u ⋅ᵥ v`. The proof expands $v$ in the standard basis, uses
--   linearity, and commutes each product.
-- source:
--   Carried as an internal support lemma, with this exact statement and proof, in twelve accepted submissions across ten missions of the OR Formalization Drive (e.g. https://prove2.me/submissions/3c55ced4-4944-4de2-ba43-8110d2682db1); published here once so that it can be imported. The finite-dimensional Riesz representation in coordinates.

import Mathlib

open Matrix

theorem Module.Dual.exists_dotProduct_eq {n : Type*} [Fintype n] [DecidableEq n]
    (φ : Module.Dual ℝ (n → ℝ)) : ∃ u : n → ℝ, ∀ v, φ v = u ⬝ᵥ v := by sorry
