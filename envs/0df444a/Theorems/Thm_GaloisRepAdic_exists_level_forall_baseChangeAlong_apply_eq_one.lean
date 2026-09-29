-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_level_forall_baseChangeAlong_apply_eq_one
-- name    : GaloisRepAdic.exists_level_forall_baseChangeAlong_apply_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/f6a0e1e6-564f-5436-b0f9-e00f6c46fc17
-- title:
--   One finite level trivialising all depth-K base changes
-- statement:
--   Let $A$ be a commutative local ring and let $\rho$ be an element of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16), that is: a free finite $A$-module $V$ of rank $2$, a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) = \overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ (automorphisms of `AlgebraicClosure ℚ`) to $\mathrm{End}_A(V)$, together with the property [`GaloisActionIsAdicContinuous`](def/GaloisRep_Adic.html#L9): for every $n$ there is an intermediate field of $\overline{\mathbb Q}/\mathbb Q$, finite over $\mathbb Q$, whose pointwise stabiliser moves every $v \in V$ only inside $\mathfrak m_A^{\,n} \cdot V$. Let $K \in \mathbb N$. The assertion is that there exists an intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$, finite-dimensional over $\mathbb Q$, such that for every commutative local ring $B$, every ring homomorphism $f : A \to B$ that is local, and every $s$ fixing $L$ pointwise, the hypothesis $f(a) = 0$ for all $a \in \mathfrak m_A^{\,K}$ forces $s$ to act as the identity on the base change $\rho.\mathrm{baseChangeAlong}\, f$, whose underlying module is $B \otimes_A V$ with $B$ an $A$-algebra via $f$ and with $s$ acting by $\mathrm{id}_B \otimes \rho(s)$. Thus one finite level $L$, depending only on $\rho$ and $K$, works simultaneously for all such $f$ and $B$.
--
--   This is the uniformity statement extracted from $\mathfrak m$-adic continuity: the level needed to trivialise a base change of $\rho$ depends only on the depth $K$ at which the maximal ideal is killed, not on the target local ring. It is used by [`GaloisRep.DeformationRingData.exists_localInvariant_of_ordinaryLine`](thm.html#GaloisRep.DeformationRingData.exists_localInvariant_of_ordinaryLine), where characters arising on base changes along truncating local homomorphisms must be seen to factor through a fixed finite extension of $\mathbb Q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_level_forall_baseChangeAlong_apply_eq_one.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.exists_level_forall_baseChangeAlong_apply_eq_one
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) (K : ℕ) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ {B : Type} [CommRing B] [IsLocalRing B] (f : A →+* B) (hf : IsLocalHom f),
        (∀ a ∈ IsLocalRing.maximalIdeal A ^ K, f a = 0) →
        ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, s x = x) →
          (ρ.baseChangeAlong f hf).ρ s = 1 := by sorry
