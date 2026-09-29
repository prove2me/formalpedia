-- Prove2me | Theorems.Thm_GaloisRepAdic_residual_baseChangeAlong_apply_ne_one
-- name    : GaloisRepAdic.residual_baseChangeAlong_apply_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/58e391a2-785c-5495-9296-4b3c96617aea
-- title:
--   Residual non-triviality persists under base change of coefficients
-- statement:
--   Let $A$ and $B$ be commutative local rings and let $\varphi : A \to B$ be a ring homomorphism which is local (non-units of $A$ are sent to non-units of $B$). Let $\rho$ be an object of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16), that is: a free $A$-module $V$ of finite type with $\operatorname{rank}_A V = 2$, a monoid homomorphism $\rho$ from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\mathrm{End}_A(V)$, and the adic continuity condition that for every $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak m_A^n \cdot V$ for all $v \in V$. Let $\sigma$ be an automorphism of $\overline{\mathbb Q}$ over $\mathbb Q$ and suppose that the residual representation of $\rho$, namely $\mathrm{ResidueField}(A) \otimes_A V$ with $\sigma$ acting by the base change of $\rho(\sigma)$, sends $\sigma$ to an endomorphism different from the identity. Then the same holds for the representation obtained by first extending scalars along $\varphi$ to $B \otimes_A V$ and then passing to the residual representation over $\mathrm{ResidueField}(B)$: the image of $\sigma$ there is not the identity.
--
--   This records that a witness of residual non-triviality for a single Galois element is preserved when the coefficient ring of a two-dimensional adic representation is changed along a local homomorphism, for instance when passing from $A$ to a quotient $A/I$ or to a larger coefficient ring. It is used in the verification of the strict ordinarity condition from the ordinarity condition together with a residual très-ramifiée hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_residual_baseChangeAlong_apply_ne_one.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.residual_baseChangeAlong_apply_ne_one
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (h : ρ.residual.ρ σ ≠ 1) :
    (ρ.baseChangeAlong φ hφ).residual.ρ σ ≠ 1 := by sorry
