-- Prove2me | Theorems.Thm_MvPolynomial_exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization
-- name    : MvPolynomial.exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/512c1542-52eb-5138-a5d5-338902786f33
-- title:
--   Differentials of a localised polynomial ring after base change
-- statement:
--   Let $R$ be a commutative ring, let $n$ be a natural number, write $P_0 = R[x_0,\dots,x_{n-1}]$ for the polynomial ring `MvPolynomial (Fin n) R`, and let $M \subseteq P_0$ be a submonoid. Let $P$ be a commutative ring that is a $P_0$-algebra and a localisation of $P_0$ at $M$, and also an $R$-algebra in such a way that $R \to P_0 \to P$ is compatible with the $R$-algebra structure on $P$. Let $K$ be a commutative ring that is both a $P$-algebra and a $P_0$-algebra, compatibly, i.e. $P_0 \to P \to K$ agrees with the structure map $P_0 \to K$. The assertion is that there exists a $K$-linear isomorphism
--   $$e : K \otimes_P \Omega_{P/R} \;\xrightarrow{\ \sim\ }\; K^n$$
--   (with $K^n$ the functions $\mathrm{Fin}\,n \to K$) such that for every polynomial $a \in P_0$ one has
--   $$e\bigl(1 \otimes d_{R}(\text{image of }a\text{ in }P)\bigr) = \bigl(i \mapsto \text{image in }K\text{ of }\partial a/\partial x_i\bigr),$$
--   where $\partial a/\partial x_i$ is `MvPolynomial.pderiv i a`. Only the existence of such an $e$ is asserted, not a canonical choice.
--
--   This is the freeness of the module of Kähler differentials of a localised polynomial algebra, together with the identification of the universal derivation with the tuple of partial derivatives: the computation underlying the Jacobian criterion. It is used in the verification that a quotient of a localisation of a polynomial ring at a prime is formally smooth once the relevant partial derivatives lie in the appropriate ideal, via [`MvPolynomial.formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem`](thm.html#MvPolynomial.formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPolynomial TensorProduct KaehlerDifferential

theorem MvPolynomial.exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization
    (R : Type) [CommRing R] {n : ℕ} (M : Submonoid (MvPolynomial (Fin n) R))
    (P : Type) [CommRing P] [Algebra (MvPolynomial (Fin n) R) P] [IsLocalization M P]
    [Algebra R P] [IsScalarTower R (MvPolynomial (Fin n) R) P]
    (K : Type) [CommRing K] [Algebra P K] [Algebra (MvPolynomial (Fin n) R) K]
    [IsScalarTower (MvPolynomial (Fin n) R) P K] :
    ∃ e : K ⊗[P] Ω[P⁄R] ≃ₗ[K] (Fin n → K),
      ∀ a : MvPolynomial (Fin n) R,
        e ((1 : K) ⊗ₜ[P] KaehlerDifferential.D R P (algebraMap (MvPolynomial (Fin n) R) P a)) =
          fun i => algebraMap (MvPolynomial (Fin n) R) K (MvPolynomial.pderiv i a) := by sorry
