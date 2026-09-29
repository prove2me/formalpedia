-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_hom
-- name    : GoodReductionJacobian.RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_hom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/e057be13-527b-5eaf-b0a3-7d1095651d9b
-- title:
--   Negation commutes with a homomorphism of relative group laws
-- statement:
--   Let $\varphi : S_1 \to S_2$ be a homomorphism of commutative rings, and let $f_1 : A_1 \to \operatorname{Spec} S_1$ and $f_2 : A_2 \to \operatorname{Spec} S_2$ be morphisms of schemes, each equipped with a relative group law, $L_1$ for $f_1$ and $L_2$ for $f_2$: that is, a functorial group structure on the sets $\mathrm{SchemeHomOver}\, t\, f = \{\psi : T \to A \mid \psi \circ f = t\}$ of $T$-points over each $t : T \to \operatorname{Spec} S_i$, given by operations $\mathrm{mul}$, $\mathrm{one}$, $\mathrm{inv}$ satisfying associativity, the two unit laws, left inverse cancellation, and naturality of $\mathrm{mul}$ under precomposition with a morphism $\psi : T' \to T$ over the base. Let $v : A_2 \to A_1$ satisfy $v$ followed by $f_1$ equals $f_2$ followed by $\operatorname{Spec}(\varphi)$, and assume $v$ is multiplicative on points: for every scheme $T$, every $t : T \to \operatorname{Spec} S_2$ and all $T$-points $P, Q$ of $A_2$ over $t$, the underlying morphism of $L_2.\mathrm{mul}\, t\, P\, Q$ followed by $v$ equals the underlying morphism of $L_1.\mathrm{mul}$ at the base point $t$ followed by $\operatorname{Spec}(\varphi)$, applied to the $T$-points $P.1 \circ\! \to\! v$ and $Q.1$ followed by $v$ of $A_1$. Then $v$ followed by $\mathrm{negMor}\, f_1\, L_1$ equals $\mathrm{negMor}\, f_2\, L_2$ followed by $v$, where $\mathrm{negMor}\, f\, L$ denotes the underlying morphism of $L.\mathrm{inv}\, f\, (\mathrm{idPt}\, f)$, the inverse of the identity point $\mathbb{1}_A$ viewed as an $A$-point of $A$ over $f$. Everything takes place in schemes of universe level $0$.
--
--   This is the statement that a morphism which is a homomorphism on points in the sense above intertwines the negation morphisms $[-1]$ of the two relative group laws, with no cartesian or flatness hypothesis on $v$. It is used in the polarisation and Rosati material, for instance in the reductions of the existence of a faithfully flat principal square root to pullbacks over discrete valuation rings and to clopen pieces of the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_hom.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_hom
    {S₁ S₂ : Type} [CommRing S₁] [CommRing S₂] (φ : S₁ →+* S₂)
    {A₁ A₂ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of S₁)} {f₂ : A₂ ⟶ Spec (CommRingCat.of S₂)}
    (L₁ : RelativeGroupLaw S₁ f₁) (L₂ : RelativeGroupLaw S₂ f₂)
    (v : A₂ ⟶ A₁) (hv : v ≫ f₁ = f₂ ≫ Spec.map (CommRingCat.ofHom φ))
    (hom : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S₂)) (P Q : SchemeHomOver t f₂),
      (L₂.mul t P Q).1 ≫ v =
        (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ v, by rw [Category.assoc, hv, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ v, by rw [Category.assoc, hv, ← Category.assoc, Q.2]⟩).1) :
    v ≫ negMor f₁ L₁ = negMor f₂ L₂ ≫ v := by sorry
