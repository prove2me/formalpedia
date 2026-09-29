-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_cover_comp_eq_comp_finComb_of_nsmul_eq_one_of_etale
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_cover_comp_eq_comp_finComb_of_nsmul_eq_one_of_etale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/0a32a82b-850f-57dc-bf93-20a05367a539
-- title:
--   Zariski-local exhaustion of n-torsion by finitely many torsion sections
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, $f : A \to \operatorname{Spec} S$ a morphism, and $L$ a relative group law for $f$: a functorial group structure (multiplication, unit, inverse, associativity, unit laws, left inverses, and compatibility with base change along morphisms of test schemes over $\operatorname{Spec} S$) on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points of $A$ over each $t : T \to \operatorname{Spec} S$; assume $L$ is commutative, and fix $n \in \mathbb{N}$, where $n$-fold iteration of the multiplication against a point is written $n \cdot y$. Assume given a finite étale $S$-algebra $B$ and a closed immersion $\iota : \operatorname{Spec} B \to A$ over $\operatorname{Spec} S$ representing the $n$-torsion: for every test scheme $T$, every $t : T \to \operatorname{Spec} S$ and every $T$-point $y$ of $A$ over $t$, one has $n \cdot y = e$ if and only if $y$ factors through $\iota$. Let $S'$ be an $S$-algebra and $P_1,\dots,P_m$ points of $A$ over $\operatorname{Spec} S'$ with $n \cdot P_i = e$, and assume these exhaust the $n$-torsion at geometric points: for every algebraically closed field $k$, every ring homomorphism $sk : S' \to k$ and every point $Q$ of $A$ over $\operatorname{Spec} k$ (structured by $sk$ composed with $S \to S'$) with $n \cdot Q = e$, there are exponents $c_i \in \{0,\dots,n-1\}$ such that the base change along $\operatorname{Spec} sk$ of the product $\prod_i P_i^{c_i}$ (formed in the group of points over $\operatorname{Spec} S'$) equals $Q$. Then for every $S'$-algebra $R$ and every point $y$ of $A$ over $\operatorname{Spec} R$ with $n \cdot y = e$, there exist $M \in \mathbb{N}$ and $r_1,\dots,r_M \in R$ generating the unit ideal of $R$ such that for each $j$ there are exponents $c_i \in \{0,\dots,n-1\}$ with the localisation morphism $\operatorname{Spec} R[1/r_j] \to \operatorname{Spec} R$ followed by $y$ equal to the morphism $\operatorname{Spec} R[1/r_j] \to \operatorname{Spec} S'$ followed by $\prod_i P_i^{c_i}$.
--
--   This is the passage from exhaustion of the $n$-torsion by a fixed finite family of torsion sections at geometric points to exhaustion Zariski-locally over an arbitrary base algebra, the finite étale hypothesis on the torsion subscheme entering through the separability idempotent (equivalently, the open and closed diagonal of $\operatorname{Spec} B$ over $\operatorname{Spec} S$). It feeds the construction of étale torsion and type-group data for abelian schemes, being used in [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_etale_typeGroup_nsmul_eq_one_iff_of_isUnit`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_etale_typeGroup_nsmul_eq_one_iff_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_cover_comp_eq_comp_finComb_of_nsmul_eq_one_of_etale.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_cover_comp_eq_comp_finComb_of_nsmul_eq_one_of_etale
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative) (n : ℕ)

    (B : Type) [CommRing B] [Algebra S B] [Module.Finite S B] [Algebra.Etale S B]
    (ι : Spec (CommRingCat.of B) ⟶ A) (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S B)))
    (hιc : IsClosedImmersion ι)
    (hιn : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (y : SchemeHomOver t f),
      L.nsmul t n y = L.one t ↔ ∃ z : T ⟶ Spec (CommRingCat.of B), z ≫ ι = y.1)

    (S' : Type) [CommRing S'] [Algebra S S'] {m : ℕ}
    (P : Fin m → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S S'))) f)
    (hP : ∀ i, L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap S S'))) n (P i) =
      L.one (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (hspan : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k)
      (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S S')))) f),
      L.nsmul (Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S S')))) n Q =
        L.one (Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S S')))) →
      ∃ c : Fin m → Fin n,
        Spec.map (CommRingCat.ofHom sk) ≫
          (L.finComb (Spec.map (CommRingCat.ofHom (algebraMap S S'))) P (fun i => (c i : ℕ))).1 = Q.1)

    (R : Type) [CommRing R] [Algebra S' R]
    (y : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap S' R).comp (algebraMap S S')))) f)
    (hy : L.nsmul (Spec.map (CommRingCat.ofHom ((algebraMap S' R).comp (algebraMap S S')))) n y =
      L.one (Spec.map (CommRingCat.ofHom ((algebraMap S' R).comp (algebraMap S S'))))) :
    ∃ (M : ℕ) (r : Fin M → R), Ideal.span (Set.range r) = ⊤ ∧ ∀ j, ∃ c : Fin m → Fin n,
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (r j)))) ≫ y.1 =
        Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away (r j))).comp (algebraMap S' R))) ≫
          (L.finComb (Spec.map (CommRingCat.ofHom (algebraMap S S'))) P (fun i => (c i : ℕ))).1 := by sorry
