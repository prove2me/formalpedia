-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker
-- name    : GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/554734a2-a40d-5789-a12f-d0a6335e290d
-- title:
--   Uniqueness of lifts of homomorphisms along nilpotent thickenings
-- statement:
--   Let $S$ be a commutative ring, let $f : A \to \operatorname{Spec} S$ and $g : B \to \operatorname{Spec} S$ be morphisms of schemes (all in universe $0$), and let `LA`, `LB` be relative group laws on $f$ and on $g$: for every $T$ and every $t : T \to \operatorname{Spec} S$ a group structure (`mul`, `one`, `inv` with associativity, unit and inverse laws) on the set of $t$-sections $\{\varphi : T \to A \mid \varphi \circ\! f = t\}$, compatible with precomposition in $T$; both laws are assumed commutative. Both $f$ and $g$ are assumed to satisfy `AbelianSchemePropertyBundle`: smooth, proper, with connected fibres $f^{-1}(\{s\})$ over every point of the base, and admitting some relative group law. Let $\psi : S' \to S''$ be a surjective ring homomorphism whose kernel satisfies $(\ker \psi)^n = \bot$ for some $n$, and let $s : \operatorname{Spec} S' \to \operatorname{Spec} S$. Let $\varphi_1, \varphi_2 : A \times_{\operatorname{Spec} S} \operatorname{Spec} S' \to B$ be morphisms over $s$, i.e. $\varphi_i$ followed by $g$ equals the second projection followed by $s$, and assume each $\varphi_i$ is a homomorphism of the group laws on points: for all $T$, $t' : T \to \operatorname{Spec} S'$ and sections $P, Q$ of $f$ over $t'$ followed by $s$, the section induced by `LA.mul` $P\,Q$ composed with $\varphi_i$ equals `LB.mul` of the sections induced by $P$ and by $Q$ composed with $\varphi_i$. If the base changes of $\varphi_1$ and $\varphi_2$ along $\operatorname{Spec}\psi$, that is their precompositions with the map $A \times_{\operatorname{Spec} S} \operatorname{Spec} S'' \to A \times_{\operatorname{Spec} S} \operatorname{Spec} S'$ induced by $\operatorname{id}_A$ and $\operatorname{Spec}\psi$, agree, then $\varphi_1 = \varphi_2$.
--
--   This is the functor-of-points form of the statement that the scheme of homomorphisms between abelian schemes is formally unramified over the base: a homomorphism of abelian schemes is determined by its reduction modulo a nilpotent ideal. It is used in the Čerednik–Drinfeld/fake elliptic curve part of the development, where lifts of isogenies and of quaternionic actions along square-zero and nilpotent thickenings are shown to be unique.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker
    (S : Type) [CommRing S] {A B : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of S)) (g : B ⟶ Spec (CommRingCat.of S))
    (LA : RelativeGroupLaw S f) (LB : RelativeGroupLaw S g)
    (hAc : LA.IsCommutative) (hBc : LB.IsCommutative)
    (hA : AbelianSchemePropertyBundle S f) (hB : AbelianSchemePropertyBundle S g)
    (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'') (hψ : Function.Surjective ψ)
    (hnil : ∃ n : ℕ, RingHom.ker ψ ^ n = ⊥)
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (φ₁ φ₂ : pullback f s ⟶ B) (hφ₁ : φ₁ ≫ g = pullback.snd f s ≫ s) (hφ₂ : φ₂ ≫ g = pullback.snd f s ≫ s)
    (hhom₁ : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
        pullback.lift (LA.mul (t' ≫ s) P Q).1 t' (LA.mul (t' ≫ s) P Q).2 ≫ φ₁ =
          (LB.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ φ₁, by rw [Category.assoc, hφ₁, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ φ₁, by rw [Category.assoc, hφ₁, ← Category.assoc, pullback.lift_snd]⟩).1)
    (hhom₂ : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
        pullback.lift (LA.mul (t' ≫ s) P Q).1 t' (LA.mul (t' ≫ s) P Q).2 ≫ φ₂ =
          (LB.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ φ₂, by rw [Category.assoc, hφ₂, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ φ₂, by rw [Category.assoc, hφ₂, ← Category.assoc, pullback.lift_snd]⟩).1)

    (hred : pullback.map f (Spec.map (CommRingCat.ofHom ψ) ≫ s) f s (𝟙 A) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
              (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id]) ≫ φ₁ =
            pullback.map f (Spec.map (CommRingCat.ofHom ψ) ≫ s) f s (𝟙 A) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
              (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id]) ≫ φ₂) :
    φ₁ = φ₂ := by sorry
