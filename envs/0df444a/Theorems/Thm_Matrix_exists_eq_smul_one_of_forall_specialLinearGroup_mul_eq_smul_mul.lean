-- Prove2me | Theorems.Thm_Matrix_exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul
-- name    : Matrix.exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/0318e932-bd39-51b2-8b6c-8d79a54efba1
-- title:
--   Matrices projectively commuting with SL₂(ℤ/q) are scalar
-- statement:
--   Let $q$ be a natural number, let $k$ be a field, and let $\varphi : \mathbb{Z}/q \to k$ be a ring homomorphism (no injectivity, and no condition on $q$, is assumed). Let $B$ be a $2\times 2$ matrix over $k$ with $\det B \neq 0$. Assume that for every $\gamma$ in the special linear group $SL_2(\mathbb{Z}/q)$ there exists a scalar $c \in k$, allowed to depend on $\gamma$ and not assumed nonzero, such that $B \cdot \varphi(\gamma) = c \cdot (\varphi(\gamma) \cdot B)$, where $\varphi(\gamma)$ denotes the matrix over $k$ obtained by applying $\varphi$ to each entry of the underlying matrix of $\gamma$ and the right-hand side is the scalar multiple by $c$ of the product $\varphi(\gamma)\cdot B$. The conclusion is that there exists $a \in k$ with $B = a \cdot 1$, i.e. $B$ is the scalar multiple by $a$ of the $2 \times 2$ identity matrix.
--
--   This is the elementary statement that an invertible $2\times 2$ matrix lying in the projective centraliser of the image of $SL_2(\mathbb{Z}/q)$ is a scalar matrix; it serves as a triviality statement for that centraliser. It is used in the construction of local charts on the Drinfeld curve, to compare the linear parts of semilinear transport data attached to two chart witnesses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul
    (q : ℕ) (k : Type) [Field k] (φ : ZMod q →+* k)
    (B : Matrix (Fin 2) (Fin 2) k) (hB : B.det ≠ 0)
    (h : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) (ZMod q), ∃ c : k,
      B * (γ : Matrix (Fin 2) (Fin 2) (ZMod q)).map φ = c • ((γ : Matrix (Fin 2) (Fin 2) (ZMod q)).map φ * B)) :
    ∃ a : k, B = a • (1 : Matrix (Fin 2) (Fin 2) k) := by sorry
