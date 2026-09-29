-- Prove2me | Theorems.Thm_GaloisRepAdic_isUnramifiedAt_of_forall_quotient
-- name    : GaloisRepAdic.isUnramifiedAt_of_forall_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/8ffabf61-41e4-5fd7-923e-6e8af5263011
-- title:
--   Unramifiedness descends from the Artinian quotients A/𝔪^{m+1}
-- statement:
--   Let $A$ be a Noetherian commutative local ring with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal A`, let $\rho$ be a [`GaloisRepAdic`](def/GaloisRep_Adic.html#L16) over $A$ — that is, a finite free $A$-module $V$ with $\operatorname{rank}_A V = 2$ together with a monoid homomorphism $\rho$ from $\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ (the automorphisms of `AlgebraicClosure ℚ` over $\mathbb Q$) to $\operatorname{End}_A V$ satisfying the adic continuity condition [`GaloisActionIsAdicContinuous`](def/GaloisRep_Adic.html#L9): for each $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak m^n \cdot V$ for all $v \in V$ — and let $q$ be a natural number. Assume that for every $m$ the base change of $\rho$ along the quotient map $A \to A/\mathfrak m^{m+1}$ (a surjective, hence local, homomorphism onto a nontrivial local ring), namely the representation on $(A/\mathfrak m^{m+1}) \otimes_A V$ given by the base-changed endomorphisms, is unramified at $q$. Then $\rho$ itself is unramified at $q$: for every valuation subring $P$ of $\overline{\mathbb Q}$ with $q$ a nonunit of $P$, and every $\sigma$ in the image in $\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ of the inertia subgroup of $P$ over $\mathbb Q$, one has $\rho(\sigma) = 1$.
--
--   This is the passage to the limit along the cofinal family of Artinian quotients $A/\mathfrak m^{m+1}$ for the unramifiedness clause of a local deformation condition, in the style of Mazur's axioms for deformation problems; the converse direction is the corresponding base-change statement. It is cited by the analogous descent statements for the flat, ordinary and strictly ordinary conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isUnramifiedAt_of_forall_quotient.lean

import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.isUnramifiedAt_of_forall_quotient {A : Type} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (ρ : GaloisRepAdic A) {q : ℕ}
    (h : ∀ m : ℕ,
      haveI : Nontrivial (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
          (Ideal.IsMaximal.ne_top inferInstance) (Ideal.pow_le_self (Nat.succ_ne_zero m)))
      haveI : IsLocalRing (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      (ρ.baseChangeAlong (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (m + 1)))
          (IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective)).IsUnramifiedAt q) :
    ρ.IsUnramifiedAt q := by sorry
