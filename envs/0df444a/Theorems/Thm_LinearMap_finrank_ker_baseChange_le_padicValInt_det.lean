-- Prove2me | Theorems.Thm_LinearMap_finrank_ker_baseChange_le_padicValInt_det
-- name    : LinearMap.finrank_ker_baseChange_le_padicValInt_det
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/b6bec9ab-4e99-5afa-a10b-e3bf846f4754
-- title:
--   Kernel of a base-changed integral endomorphism and vₚ(det)
-- statement:
--   Let $L$ be an additive commutative group that is a free and finitely generated $\mathbb{Z}$-module, and let $A : L \to L$ be a $\mathbb{Z}$-linear endomorphism whose determinant $\det A \in \mathbb{Z}$ is non-zero. Let $p$ be a prime number and let $F$ be a field of characteristic $p$. Form the base change $A \otimes \mathrm{id}_F$, the $F$-linear endomorphism of $F \otimes_{\mathbb{Z}} L$ induced by $A$ (in Lean, `A.baseChange F`). The assertion is an inequality between natural numbers: the $F$-dimension of the kernel of $A \otimes \mathrm{id}_F$, as a subspace of $F \otimes_{\mathbb{Z}} L$, is at most $\operatorname{padicValInt} p (\det A)$, the exponent of $p$ in the factorisation of the integer $\det A$. No hypothesis relating $F$ to $\mathbb{Z}/p$ beyond its characteristic is imposed, and $F$ is not assumed perfect, algebraically closed or finite.
--
--   This is the elementary bound $\dim_F \ker(A \otimes F) \le v_p(\det A)$ for an endomorphism of a finite free $\mathbb{Z}$-lattice with non-zero determinant, a quantitative form of the statement that the index of $A(L)$ in $L$ is $|\det A|$. It is used in the study of mod $p$ modular forms, where it bounds the dimension of the kernel of a Hecke operator acting on a space of mod $p$ cusp forms, via [`ModPForms.finrank_ker_heckeU_modPCusp_mul_two_le_finrank_modPCusp_two`](thm.html#ModPForms.finrank_ker_heckeU_modPCusp_mul_two_le_finrank_modPCusp_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_finrank_ker_baseChange_le_padicValInt_det.lean

import Mathlib.LinearAlgebra.Determinant
import Mathlib.NumberTheory.Padics.PadicVal.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LinearMap.finrank_ker_baseChange_le_padicValInt_det
    {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (A : L →ₗ[ℤ] L) (hA : LinearMap.det A ≠ 0) (p : ℕ) [Fact p.Prime]
    (F : Type) [Field F] [CharP F p] :
    Module.finrank F ↥(LinearMap.ker (A.baseChange F)) ≤ padicValInt p (LinearMap.det A) := by sorry
