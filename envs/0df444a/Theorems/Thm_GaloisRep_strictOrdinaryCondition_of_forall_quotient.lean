-- Prove2me | Theorems.Thm_GaloisRep_strictOrdinaryCondition_of_forall_quotient
-- name    : GaloisRep.strictOrdinaryCondition_of_forall_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/199c3073-34e1-51e6-8252-4272c0bcef6c
-- title:
--   Strict ordinariness detected on the quotients A/𝔪^{m+1}
-- statement:
--   Let $A$ be a Noetherian local commutative ring with maximal ideal $\mathfrak m$, let $\mathcal O$ be a commutative ring with an $\mathcal O$-algebra structure on $A$ (which enters only through the typing of the condition), and let $\rho$ be an object of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16), that is, a finite free $A$-module $V$ of rank $2$ together with a monoid homomorphism from $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\operatorname{End}_A(V)$ which is $\mathfrak m$-adically continuous in the sense that for each $n$ some finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$ has the property that its pointwise stabiliser acts trivially on $V/\mathfrak m^n V$. Let $p$ be an odd prime and $S$ a finite set of natural numbers. Assume that for every $m$ the representation obtained from $\rho$ by base change along the (local, surjective) quotient map $A \to A/\mathfrak m^{m+1}$, i.e. the action on $(A/\mathfrak m^{m+1}) \otimes_A V$, satisfies [`GaloisRep.strictOrdinaryCondition 𝒪 p S`](def/GaloisRep_StrictOrdinary.html#L28). Then $\rho$ itself satisfies that condition, namely: $p \in \mathfrak m$ and for all $n$, every $\sigma$ acting on $p^n$-th roots of unity by $\mu \mapsto \mu^{a}$ satisfies $\det \rho(\sigma) - a \in (p^n)$; for every valuation subring $P$ of $\overline{\mathbb Q}$ lying over $p$ there is a line $L = A\cdot b_0$ spanned by a member of an $A$-basis of $V$, stable under the decomposition subgroup of $P$, with $\rho(\sigma)v - v \in L$ for $\sigma$ in the inertia subgroup, and such that each $\sigma$ in the decomposition subgroup has scalars $x$ on $L$ and $z$ on $V/L$ with $x - a z \in (p^n)$ whenever $\sigma$ acts by $\mu \mapsto \mu^a$ on $p^n$-th roots of unity; and $\rho$ is unramified at every prime $q \notin S$, in the sense that inertia at every valuation subring over $q$ acts trivially.
--
--   This is the continuity (or limit) clause in the verification that the strict ordinary condition of type $S$ is a deformation condition in Mazur's sense: a property imposed on all Artinian quotients $A/\mathfrak m^{m+1}$ propagates to the Noetherian local ring $A$ itself. It is used by [`GaloisRep.isDeformationCondition_strictOrdinaryCondition`](thm.html#GaloisRep.isDeformationCondition_strictOrdinaryCondition), and assembles the corresponding statements for the cyclotomic determinant, strict ordinariness at $p$ and unramifiedness outside $S$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_strictOrdinaryCondition_of_forall_quotient.lean

import Mathlib
import Definitions.Def_GaloisRep_StrictOrdinary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRep.strictOrdinaryCondition_of_forall_quotient
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A] (ρ : GaloisRepAdic A) {p : ℕ} {S : Finset ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ∀ m : ℕ,
      haveI : Nontrivial (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
          (Ideal.IsMaximal.ne_top inferInstance) (Ideal.pow_le_self (Nat.succ_ne_zero m)))
      haveI : IsLocalRing (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      GaloisRep.strictOrdinaryCondition 𝒪 p S
        (ρ.baseChangeAlong (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (m + 1)))
          (IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective))) :
    GaloisRep.strictOrdinaryCondition 𝒪 p S ρ := by sorry
