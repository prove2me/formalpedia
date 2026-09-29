-- Prove2me | Theorems.Thm_GaloisRepAdic_isUnipotentOnInertiaAt_of_forall_quotient
-- name    : GaloisRepAdic.isUnipotentOnInertiaAt_of_forall_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/d120e6d2-1576-5157-955a-fc3f5a5ee1e7
-- title:
--   Unipotence on inertia descends from all 𝔪^{m+1}-quotients
-- statement:
--   Let $A$ be a Noetherian commutative local ring with maximal ideal $\mathfrak{m} =$ `IsLocalRing.maximalIdeal A`, let $\rho$ be an element of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16), that is a free finite $A$-module $V$ of rank $2$ together with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = (\mathrm{AlgebraicClosure}\ \mathbb{Q} \simeq_{\mathrm{alg}[\mathbb{Q}]} \mathrm{AlgebraicClosure}\ \mathbb{Q})$ to $\mathrm{End}_A(V)$ which is adically continuous in the sense that for each $n$ there is a finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak{m}^n \cdot V$ for all $v$, and let $q$ be a natural number. Assume that for every $m$ the base change of $\rho$ along the quotient map $A \to A/\mathfrak{m}^{m+1}$ (a surjective, hence local, ring homomorphism onto a nontrivial local ring), namely $(A/\mathfrak{m}^{m+1}) \otimes_A V$ with $\sigma$ acting by $\rho(\sigma) \otimes 1$, satisfies `IsUnipotentOnInertiaAt q`. The conclusion is that $\rho$ itself satisfies `IsUnipotentOnInertiaAt q`: for every valuation subring $P$ of $\overline{\mathbb{Q}}$ with the image of $q$ lying in the nonunits of $P$, and every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$ over $\mathbb{Q}$ (a subgroup of the decomposition subgroup), the characteristic polynomial of $\rho(\sigma)$ on $V$ equals $(X-1)^2$.
--
--   This is the descent through the Artinian quotients $A/\mathfrak{m}^{m+1}$ of the local condition 'unipotent on inertia at $q$', one of the verifications needed when checking that such a condition is a deformation condition in Mazur's sense. It is used by the constructions of deformation data combining the unipotence condition with the flat, ordinary and strictly ordinary conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isUnipotentOnInertiaAt_of_forall_quotient.lean

import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.isUnipotentOnInertiaAt_of_forall_quotient {A : Type} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (ρ : GaloisRepAdic A) {q : ℕ}
    (h : ∀ m : ℕ,
      haveI : Nontrivial (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
          (Ideal.IsMaximal.ne_top inferInstance) (Ideal.pow_le_self (Nat.succ_ne_zero m)))
      haveI : IsLocalRing (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      (ρ.baseChangeAlong (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (m + 1)))
          (IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective)).IsUnipotentOnInertiaAt q) :
    ρ.IsUnipotentOnInertiaAt q := by sorry
