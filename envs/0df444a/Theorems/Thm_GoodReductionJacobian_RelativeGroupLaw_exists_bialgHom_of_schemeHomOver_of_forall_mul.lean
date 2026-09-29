-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_bialgHom_of_schemeHomOver_of_forall_mul
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_bialgHom_of_schemeHomOver_of_forall_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/7567e0fe-65f0-544d-86d0-711fbac658e5
-- title:
--   Functoriality of the coordinate Hopf algebra of relative group laws
-- statement:
--   Let $R$ be a commutative ring, and let $g \colon A \to \operatorname{Spec} R$ and $g' \colon A' \to \operatorname{Spec} R$ be affine morphisms of schemes equipped with relative group laws $L$, $L'$: that is, for every scheme $T$ and every $t \colon T \to \operatorname{Spec} R$ a multiplication, unit and inversion on the set of $T$-points $\{\varphi \colon T \to A \mid \varphi \circ g = t\}$ (respectively for $g'$), satisfying associativity, both unit laws, left inverse, and naturality under precomposition with morphisms $\psi \colon T' \to T$ over $\operatorname{Spec} R$. Let $u \colon A' \to A$ satisfy $u \circ g = g'$, and assume $u$ is a homomorphism on points: for all $t \colon T \to \operatorname{Spec} R$ and all $T$-points $x,y$ of $A'$ over $t$, composing $L'$-multiplication of $x,y$ with $u$ equals the $L$-multiplication of $x \circ u$ and $y \circ u$. Let $H$, $H'$ be commutative rings with Hopf algebra structures over $R$. Since $g$, $g'$ are affine over the affine base, $A$ and $A'$ are affine, and $\Gamma(A,\top)$, $\Gamma(A',\top)$ carry the $R$-algebra structures induced by $g$, $g'$. Then for all $R$-algebra isomorphisms $\mathrm{iso} \colon H \cong \Gamma(A,\top)$, $\mathrm{iso}' \colon H' \cong \Gamma(A',\top)$ and all families of bijections $e$ (resp. $e'$), indexed by commutative $R$-algebras $T$, between the convolution monoid of $R$-algebra maps $H \to T$ (resp. $H' \to T$) and the $T$-points of $A$ (resp. $A'$) over $\operatorname{Spec} R$, such that the morphism underlying $e\,T\,\varphi$ is $\operatorname{Spec}$ of $\varphi \circ \mathrm{iso}^{-1}$ followed by the inverse of $A \cong \operatorname{Spec} \Gamma(A,\top)$ (and likewise for $e'$), and such that $e\,T$ and $e'\,T$ carry convolution products to $L$- and $L'$-multiplication, there exists an $R$-bialgebra homomorphism $\psi \colon H \to H'$ with: $\mathrm{iso}'(\psi(h)) = \Gamma(u)(\mathrm{iso}(h))$ for all $h \in H$, where $\Gamma(u)$ is the map on global sections induced by $u$; for every commutative $R$-algebra $T$ and every $\varphi' \colon H' \to T$, the morphism underlying $e\,T$ applied to $\varphi' \circ \psi$ equals the morphism underlying $e'\,T\,\varphi'$ followed by $u$; and $\psi$ is surjective whenever $u$ is a closed immersion.
--
--   This is the Yoneda-style functoriality of the dictionary between affine group schemes over $R$ and their coordinate Hopf algebras: a morphism of schemes which is a homomorphism on points is transported into a bialgebra homomorphism of coordinate rings, compatibly with the identifications of points with algebra homomorphisms, and closed immersions become surjections. It is used in the construction of the Hopf-algebra tower attached to the identity component of the Néron model of $J_0$ together with the level maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_bialgHom_of_schemeHomOver_of_forall_mul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_bialgHom_of_schemeHomOver_of_forall_mul
    {R : Type u} [CommRing R]
    {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R g) [IsAffineHom g]
    {A' : Scheme.{u}} {g' : A' ⟶ Spec (CommRingCat.of R)} (L' : RelativeGroupLaw R g') [IsAffineHom g']
    (u : SchemeHomOver g' g)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g'),
      (⟨(L'.mul t x y).1 ≫ u.1, by rw [Category.assoc, u.2, (L'.mul t x y).2]⟩ : SchemeHomOver t g) =
        L.mul t ⟨x.1 ≫ u.1, by rw [Category.assoc, u.2, x.2]⟩ ⟨y.1 ≫ u.1, by rw [Category.assoc, u.2, y.2]⟩)
    (H : Type u) [CommRing H] [HopfAlgebra R H] (H' : Type u) [CommRing H'] [HopfAlgebra R H'] :
    letI : Algebra R Γ(A, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom.toAlgebra
    letI : Algebra R Γ(A', ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g'.appTop).hom.toAlgebra
    haveI : IsAffine A := isAffine_of_isAffineHom g
    haveI : IsAffine A' := isAffine_of_isAffineHom g'
    ∀ (iso : H ≃ₐ[R] Γ(A, ⊤)) (iso' : H' ≃ₐ[R] Γ(A', ⊤))
      (e : ∀ (T : Type u) [CommRing T] [Algebra R T],
        WithConv (H →ₐ[R] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) g)
      (e' : ∀ (T : Type u) [CommRing T] [Algebra R T],
        WithConv (H' →ₐ[R] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) g'),
      (∀ (T : Type u) [CommRing T] [Algebra R T] (φ : WithConv (H →ₐ[R] T)),
        (e T φ).1 = Spec.map (CommRingCat.ofHom ((φ.ofConv.comp (iso.symm : Γ(A, ⊤) →ₐ[R] H)).toRingHom)) ≫ A.isoSpec.inv) →
      (∀ (T : Type u) [CommRing T] [Algebra R T] (φ : WithConv (H' →ₐ[R] T)),
        (e' T φ).1 = Spec.map (CommRingCat.ofHom ((φ.ofConv.comp (iso'.symm : Γ(A', ⊤) →ₐ[R] H')).toRingHom)) ≫ A'.isoSpec.inv) →
      (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)), e T (φ * ψ) = L.mul _ (e T φ) (e T ψ)) →
      (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H' →ₐ[R] T)), e' T (φ * ψ) = L'.mul _ (e' T φ) (e' T ψ)) →
      ∃ ψ : H →ₐc[R] H',
        (∀ h : H, iso' (ψ h) = u.1.appTop.hom (iso h)) ∧
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ' : WithConv (H' →ₐ[R] T)),
          (e T (.toConv (φ'.ofConv.comp (ψ : H →ₐ[R] H')))).1 = (e' T φ').1 ≫ u.1) ∧
        (IsClosedImmersion u.1 → Function.Surjective ψ) := by sorry
