-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_compatible_univ
-- name    : GoodReductionJacobian.RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_compatible_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/84f6fb45-dc65-52f8-b25b-fd26b7ae43f3
-- title:
--   Inversion morphisms commute with base change of relative group laws
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f\colon A \to \operatorname{Spec} S$ a morphism equipped with a relative group law $L$, i.e. a group structure on the sets $\{\varphi\colon T \to A \mid \varphi \circ f = t\}$ of $A$-valued points over each $t\colon T \to \operatorname{Spec} S$, with multiplication, unit and inverse satisfying associativity, the unit laws, left inversion, and naturality of the multiplication under precomposition with $\psi\colon T' \to T$ over the base. Let $S_1, S_2$ be commutative $S$-algebras and $\varphi\colon S_1 \to S_2$ a ring homomorphism with $\varphi \circ (\text{structure map } S \to S_1) = (S \to S_2)$. Let $L_1$ and $L_2$ be relative group laws on the second projections $A \times_{\operatorname{Spec} S} \operatorname{Spec} S_i \to \operatorname{Spec} S_i$ ($i = 1, 2$). Assume the compatibility hypotheses $h_1$ and $h_2$: for every test scheme $T$, every $t'\colon T \to \operatorname{Spec} S_i$ and all points $P, Q$ of the pullback over $t'$, the first projection of $L_i.\mathrm{mul}\ t'\ P\ Q$ to $A$ agrees with the $L$-product, taken over the composite of $t'$ with $\operatorname{Spec}$ of $S \to S_i$, of the first projections of $P$ and $Q$. Let $\rho\colon A \times_{\operatorname{Spec} S} \operatorname{Spec} S_2 \to A \times_{\operatorname{Spec} S} \operatorname{Spec} S_1$ satisfy $\rho$ followed by the projection to $A$ equals the projection to $A$, and $\rho$ followed by the projection to $\operatorname{Spec} S_1$ equals the projection to $\operatorname{Spec} S_2$ followed by $\operatorname{Spec} \varphi$. Then $\rho$ followed by $\mathrm{negMor}$ of $L_1$ equals $\mathrm{negMor}$ of $L_2$ followed by $\rho$, where $\mathrm{negMor}$ of a relative group law is the underlying morphism of the inverse, under that law, of the identity point.
--
--   This is the statement that the inversion morphism $[-1]$ of a relative group law commutes with base change along a homomorphism of $S$-algebras, for base-changed laws that are compatible with the law downstairs. It is used when transporting symmetry data for line bundles — such as the isomorphism $[-1]^*\mathcal{L} \cong \mathcal{L}$ attached to a square root — between different stages of a base-change tower, and is cited in the construction of principal square roots and in the treatment of symmetric bundles on fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_compatible_univ.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_compatible_univ
    {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (S₁ S₂ : Type u) [CommRing S₁] [CommRing S₂] [Algebra S S₁] [Algebra S S₂]
    (φ : S₁ →+* S₂) (hφ : φ.comp (algebraMap S S₁) = algebraMap S S₂)
    (L₁ : RelativeGroupLaw S₁ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))))
    (L₂ : RelativeGroupLaw S₂ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₂)))))
    (h₁ : (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S₁))
          (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))),
          (L₁.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))) =
            (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₁)))
              ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (h₂ : (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S₂))
          (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₂))))),
          (L₂.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₂))) =
            (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₂)))
              ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₂))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₂))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (ρ : Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S S₂))) ⟶
          Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))
    (hρ₁ : ρ ≫ pullback.fst _ _ = pullback.fst _ _)
    (hρ₂ : ρ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ)) :
    ρ ≫ negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))) L₁ =
      negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₂)))) L₂ ≫ ρ := by sorry
