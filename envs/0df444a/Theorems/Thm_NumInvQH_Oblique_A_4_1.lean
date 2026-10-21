-- Prove2me | Theorems.Thm_NumInvQH_Oblique_A_4_1
-- name    : NumInvQH.Oblique.A_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:42.454806+00:00
-- url     : https://prove2.me/theorems/8018c0a7-6d32-448a-bec8-6e249beaa3ab
-- title:
--   Theorem A.4(1) — $q(x)=x^{\mathsf T}Cx-2x^{\mathsf T}F$ ($C\succeq0$) is bounded below on $\{Ax=b\}$, $b\in R(A)$, iff $F\in R(A^{\mathsf T})+R(C)$
-- statement:
--   Let $k,n\in\mathbb N$, $F\in\mathbb R^n$, $C\in\mathbb R^{n\times n}$ symmetric positive semidefinite, $A\in\mathbb R^{k\times n}$ and $b\in R(A)$ (so the affine subspace $\mathcal A=\{x\in\mathbb R^n: Ax=b\}$ is non-empty). Let $q(x)=x^{\mathsf T}Cx-2x^{\mathsf T}F$. Then $q$ is bounded from below on $\mathcal A$ if and only if
--
--   $$F\in R(A^{\mathsf T})+R(C).\tag{A.3}$$
--
--   Here $R(\cdot)$ is the column space and the sum is the sum of subspaces. Condition (A.3) is the solvability condition of the affinely constrained quadratic problem; in the hedging application it becomes the structure condition $b^{S\star}\in R(\tilde c^{S\star})+R(S_-)$ of Theorem 4.3(1).
--
--   **Formalization Note** "Bounded from below on $\mathcal A$" is `BddBelow` of the image $q(\mathcal A)$. Positive semidefiniteness is Mathlib's `Matrix.PosSemidef`, which includes symmetry.
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 25–26, Theorem A.4(1), eq. (A.3)

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS
import Definitions.Def_NumInvQH_Oblique_Basic

open Matrix

namespace NumInvQH.Oblique

/-- Theorem A.4(1); `b ∈ R(A)` makes the affine set non-empty. -/
theorem A_4_1 {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (b : Fin k → ℝ)
    (hb : b ∈ LinearMap.range (Matrix.toLin' A))
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosSemidef)
    (F : Fin n → ℝ) :
    BddBelow (quadraticForm C F '' {x : Fin n → ℝ | A *ᵥ x = b}) ↔
      F ∈ LinearMap.range (Matrix.toLin' Aᵀ) ⊔ LinearMap.range (Matrix.toLin' C) := by sorry

end NumInvQH.Oblique
