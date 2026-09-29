-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_schemeNsmul_comp_eq_of_forall_isTorsionPoint
-- name    : GoodReductionJacobian.RelativeGroupLaw.existsUnique_schemeNsmul_comp_eq_of_forall_isTorsionPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/27c8f44a-139e-5faa-84f6-d30086fc9fbc
-- title:
--   Dividing a homomorphism killing n-torsion by [n]
-- statement:
--   Let $S$ be a commutative ring, let $A$ be a scheme with a structure morphism $f : A \to \operatorname{Spec} S$, and let $L$ be a relative group law on $f$: a group structure on the set $\mathrm{SchemeHomOver}\ t\ f$ of morphisms $T \to A$ over $\operatorname{Spec} S$, for every $t : T \to \operatorname{Spec} S$, natural in $T$ under composition. Assume $L$ is commutative, let $n$ be a natural number, and assume the morphism `L.schemeNsmul n` $: A \to A$ — the underlying morphism of the $n$-fold $L$-multiple of the identity point $\mathrm{id}_A$ — is flat, surjective and quasi-compact. Let $f' : A' \to \operatorname{Spec} S$ carry a relative group law $L'$, and let $F : A \to A'$ satisfy $F$ followed by $f'$ equals $f$, together with two hypotheses: for all $t : T \to \operatorname{Spec} S$ and all points $P, Q$ of $A$ over $t$, the composite of $L.\mathrm{mul}\ t\ P\ Q$ with $F$ is the $L'$-product of the composites of $P$ and $Q$ with $F$; and for every point $P$ over $t$ with $L$-$n$-fold multiple equal to $L.\mathrm{one}\ t$, the composite of $P$ with $F$ is $L'.\mathrm{one}\ t$. Then there is a morphism $w : A \to A'$ with `L.schemeNsmul n` followed by $w$ equal to $F$; $w$ is the unique morphism $A \to A'$ with that property; and $w$ followed by $f'$ equals $f$, with $w$ satisfying the same multiplicativity on points over $S$ as stated for $F$.
--
--   This is the statement that multiplication by $n$ exhibits $A$ as a quotient of itself by its $n$-torsion: any homomorphism of relative group laws annihilating the $n$-torsion points factors uniquely through $[n]$, and the factorisation is again a homomorphism over $S$. It is used in the construction and rigidification of fake elliptic curves in the Čerednik–Drinfeld part of the development, where morphisms are produced by dividing a given homomorphism by $[n]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_schemeNsmul_comp_eq_of_forall_isTorsionPoint.lean

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.existsUnique_schemeNsmul_comp_eq_of_forall_isTorsionPoint
    (S : Type) [CommRing S]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative)
    (n : ℕ)
    [Flat (L.schemeNsmul n)] [Surjective (L.schemeNsmul n)] [QuasiCompact (L.schemeNsmul n)]
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of S)) (L' : RelativeGroupLaw S f')
    (F : A ⟶ A') (hF : F ≫ f' = f)
    (hFhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ F =
        (L'.mul t ⟨P.1 ≫ F, by rw [Category.assoc, hF]; exact P.2⟩
          ⟨Q.1 ≫ F, by rw [Category.assoc, hF]; exact Q.2⟩).1)
    (hFker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      L.IsTorsionPoint t n P → P.1 ≫ F = (L'.one t).1) :
    ∃ w : A ⟶ A', (L.schemeNsmul n ≫ w = F) ∧
      (∀ w' : A ⟶ A', L.schemeNsmul n ≫ w' = F → w' = w) ∧
      ∃ hw : w ≫ f' = f,
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
          (L.mul t P Q).1 ≫ w =
            (L'.mul t ⟨P.1 ≫ w, by rw [Category.assoc, hw]; exact P.2⟩
              ⟨Q.1 ≫ w, by rw [Category.assoc, hw]; exact Q.2⟩).1 := by sorry
