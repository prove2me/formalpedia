-- Prove2me | Theorems.Thm_GaloisRep_ordinaryCondition_of_forall_quotient
-- name    : GaloisRep.ordinaryCondition_of_forall_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/4bb1ff5f-d67f-574d-8076-6d0b5e467fcc
-- title:
--   Ordinary condition detected on the quotients A/𝔪^{m+1}
-- statement:
--   Let $A$ be a commutative Noetherian local ring with maximal ideal $\mathfrak m$, let $\mathcal O$ be a commutative ring with an algebra structure on $A$, let $\rho$ be a [`GaloisRepAdic`](def/GaloisRep_Adic.html#L16) over $A$ (a free $A$-module $V$ of rank $2$, finite over $A$, with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathrm{End}_A V$ that is adically continuous: for each $n$ some finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ has its fixing subgroup acting trivially modulo $\mathfrak m^n V$), let $p$ be a prime with $p \neq 2$, and let $S$ be a finite set of natural numbers. Assume that for every $m$ the base change of $\rho$ along the quotient map $A \to A/\mathfrak m^{m+1}$, which is a surjective local homomorphism onto a nontrivial local ring, satisfies [`GaloisRep.ordinaryCondition 𝒪 p S`](def/GaloisRep_LocalConditions.html#L28). Then $\rho$ satisfies [`GaloisRep.ordinaryCondition 𝒪 p S`](def/GaloisRep_LocalConditions.html#L28), that is: (i) $p \in \mathfrak m$ and for all $n$, all $\sigma$ and all $a \in \mathbb N$, if $\sigma \mu = \mu^a$ for every $p^n$-th root of unity $\mu$, then $\det \rho(\sigma) - a$ lies in $p^n A$; (ii) for every valuation subring of $\overline{\mathbb Q}$ lying over $p$ there is an $A$-line $L \subseteq V$ spanned by the first member of some basis of $V$ indexed by `Fin 2`, stable under the decomposition subgroup, with inertia acting trivially on $V/L$; (iii) $\rho$ is unramified at every prime $q \notin S$, inertia at every valuation subring over $q$ acting as the identity. The predicate's definition makes no further use of $\mathcal O$.
--
--   This is the continuity axiom, in the cofinal form "it suffices to test the quotients $A/\mathfrak m^{n}$", for the ordinary local condition in Mazur's axiomatics for deformation conditions. It is used in assembling [`GaloisRep.isDeformationCondition_ordinaryCondition`](thm.html#GaloisRep.isDeformationCondition_ordinaryCondition), the verification that the ordinary condition is a deformation condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_ordinaryCondition_of_forall_quotient.lean

import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.ordinaryCondition_of_forall_quotient
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A] (ρ : GaloisRepAdic A) {p : ℕ} {S : Finset ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ∀ m : ℕ,
      haveI : Nontrivial (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
          (Ideal.IsMaximal.ne_top inferInstance) (Ideal.pow_le_self (Nat.succ_ne_zero m)))
      haveI : IsLocalRing (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      GaloisRep.ordinaryCondition 𝒪 p S
        (ρ.baseChangeAlong (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (m + 1)))
          (IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective))) :
    GaloisRep.ordinaryCondition 𝒪 p S ρ := by sorry
