-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_compatible
-- name    : GoodReductionJacobian.RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_compatible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/ac8123fe-0825-548e-a2a0-1f3327418ee1
-- title:
--   Inversion commutes with transition maps between base changes
-- statement:
--   Let $S$ be a commutative ring, $f\colon A\to\operatorname{Spec}S$ a scheme over $S$, and $L$ a relative group law on $f$, that is, a functorial group structure on the sets $\{\varphi\colon T\to A \mid \varphi\cdot f=t\}$ of $T$-points over each $t\colon T\to\operatorname{Spec}S$. Let $S_1,S_2$ be commutative $S$-algebras and $\varphi\colon S_1\to S_2$ a ring homomorphism with $\varphi\circ(S\to S_1)=(S\to S_2)$. Let $L_1$, $L_2$ be relative group laws on the second projections of the pullbacks $A\times_{\operatorname{Spec}S}\operatorname{Spec}S_1$ and $A\times_{\operatorname{Spec}S}\operatorname{Spec}S_2$, each compatible with $L$ in the following sense: for $i=1,2$, every scheme $T$, every $t'\colon T\to\operatorname{Spec}S_i$ and all points $P,Q$ of the pullback over $t'$, the underlying morphism of the $L_i$-product of $P$ and $Q$, followed by the projection to $A$, equals the underlying morphism of the $L$-product, over $t'$ followed by $\operatorname{Spec}(S\to S_i)$, of the images of $P$ and $Q$ under the projection to $A$. Finally let $\rho\colon A\times_{\operatorname{Spec}S}\operatorname{Spec}S_2\to A\times_{\operatorname{Spec}S}\operatorname{Spec}S_1$ satisfy $\rho$ followed by the projection to $A$ equals the projection to $A$, and $\rho$ followed by the projection to $\operatorname{Spec}S_1$ equals the projection to $\operatorname{Spec}S_2$ followed by $\operatorname{Spec}\varphi$. Then $\rho$ followed by `negMor` of $L_1$ equals `negMor` of $L_2$ followed by $\rho$, where `negMor` of a relative group law is the underlying morphism $A'\to A'$ of the $L$-inverse of the identity point of $A'$ over the base.
--
--   This is the statement that the inversion $[-1]$ attached to a relative group law is compatible with the transition morphism between two base changes, for a map $S_1\to S_2$ of $S$-algebras. It is used in the polarisation material, where a symmetry isomorphism $[-1]^*\mathcal L\cong\mathcal L$ on one base change has to be transported along such transition maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_compatible.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_compatible
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (S₁ S₂ : Type) [CommRing S₁] [CommRing S₂] [Algebra S S₁] [Algebra S S₂]
    (φ : S₁ →+* S₂) (hφ : φ.comp (algebraMap S S₁) = algebraMap S S₂)
    (L₁ : RelativeGroupLaw S₁ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))))
    (L₂ : RelativeGroupLaw S₂ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₂)))))
    (h₁ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S₁))
          (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))),
          (L₁.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))) =
            (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₁)))
              ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (h₂ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S₂))
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
