-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_d_one_apply_eq_zero_of_isRegluingBy_of_isTangentCoordsOfPairAt_bare
-- name    : GoodReductionJacobian.BareDeformation.d_one_apply_eq_zero_of_isRegluingBy_of_isTangentCoordsOfPairAt_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/2787ecae-ab94-5404-8860-2486d59ab109
-- title:
--   Tangent cochain of a re-glued deformation is a cocycle
-- statement:
--   Let $B$ be a local artinian ring with algebraically closed residue field $k =$ `ResidueField B`, and let $B_1$ be a $B$-algebra whose structure map is surjective with nilpotent kernel $I =$ `RingHom.ker (algebraMap B B₁)` satisfying $I \le \mathfrak m_B$ and $I\,\mathfrak m_B = 0$. Let $f_1 : A_1 \to \operatorname{Spec} B_1$ carry a commutative relative group law $L_1$ and the abelian-scheme property bundle (smooth, proper, connected fibres, a group law), let $V$ be a finite-dimensional $k$-vector space with compatible $B$-module and opposite-scalar structures, and let $\iota : V \to B$ be an injective $B$-linear map with image $I$. Let $D_0$ be a bare deformation of $(f_1, L_1)$ to $B$ with $D_0.f$ separated, $\mathcal U$ an ordered affine open cover of $D_0.A$, $i_0$ an index, $e_0$ a section of $\mathcal U.U\,i_0$ over $\operatorname{Spec} B$ composing to the unit of $D_0.L$, and $e_1$ the analogous section of the $i_0$-th member of the base-changed cover over $\operatorname{Spec} k$ composing to the unit of the base-changed group law. Let $\sigma$ be, for each $1$-simplex $s$ of $\mathcal U$, a ring isomorphism $k \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s) \cong \Gamma$ of the base-changed intersection, compatible with pullback of sections along `pullback.fst` and with the $k$-algebra structure. Let $\tau_s$ be self-isomorphisms of the intersections $\mathcal U.\mathrm{inter}\,s$, let $D$ be a bare deformation obtained from $D_0$ by re-gluing along $\mathcal U$ and $\tau$ (`IsRegluingBy`), and let $c$ be a $k$-point-derivation at $e_1$ on the sections over the base-changed $\mathcal U.U\,i_0$, valued in $k$-linear maps from $V^\ast$ to $1$-cochains of the unit $O$-module presheaf of `pullback.snd`. Assume, for every $1$-simplex $s$, that there is a map $c_s$ which is a system of tangent coordinates of the pair consisting of the inclusion $\operatorname{Spec}\Gamma(\mathcal U.\mathrm{inter}\,s) \to D_0.A$ and its $\tau_s$-twist, in the sense of `IsTangentCoordsOfPairAt` for the data $(I, V, \iota)$, the base-changed projection, group law and $\mathcal U.U\,i_0$, and such that $\sigma_s \circ c_s$ is the $s$-component of $c$. Then for all sections $a$ over the base-changed $\mathcal U.U\,i_0$ and all $\xi \in V^\ast$, the Čech differential $d^1$ of the $1$-cochain $c(a)(\xi)$ for the unit $O$-module presheaf on the base-changed cover vanishes.
--
--   This is the cocycle condition for the tangent class attached to a deformation re-glued from a given one: the $1$-cochain of tangent coordinates read off from the re-gluing automorphisms has vanishing Čech coboundary, so it represents a class in $H^1$ of the special fibre. It feeds the existence statement [`GoodReductionJacobian.BareDeformation.exists_isRegluingBy_exists_isTangentCoordsOfPairAt_of_bareDeformation_bare`](thm.html#GoodReductionJacobian.BareDeformation.exists_isRegluingBy_exists_isTangentCoordsOfPairAt_of_bareDeformation_bare), which produces a re-gluing together with its tangent cocycle for an arbitrary deformation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_d_one_apply_eq_zero_of_isRegluingBy_of_isTangentCoordsOfPairAt_bare.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing Scheme.TwoAffineOpenCover
open scoped Quaternion TensorProduct NumberField

theorem GoodReductionJacobian.BareDeformation.d_one_apply_eq_zero_of_isRegluingBy_of_isTangentCoordsOfPairAt_bare
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [IsAlgClosed (ResidueField B)]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥)
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁) (hc₁ : L₁.IsCommutative)
    (h₁ : AbelianSchemePropertyBundle B₁ f₁)
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    [Module (ResidueField B)ᵐᵒᵖ V] [IsCentralScalar (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))

    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f]
    (𝒰 : D₀.A.OrderedAffineCover) (i₀ : 𝒰.ι) (e₀ : Spec (CommRingCat.of B) ⟶ ↑(𝒰.U i₀)) (he₀ : e₀ ≫ (𝒰.U i₀).ι = (D₀.L.one (𝟙 _)).1)

    (e₁ : Spec (CommRingCat.of (ResidueField B)) ⟶ (((𝒰.baseChange D₀.f (ResidueField B)).U i₀) : Scheme.{0}))
    (he₁ : e₁ ≫ ((𝒰.baseChange D₀.f (ResidueField B)).U i₀).ι = ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).one (𝟙 _)).1)
    (σ : ∀ s : 𝒰.Idx 1,
      letI := algebraOfHom D₀.f (𝒰.inter s)
      ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s)) ≃+* Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s))
    (hσ₁ : ∀ (s : 𝒰.Idx 1) (x : Γ(D₀.A, 𝒰.inter s)),
      letI := algebraOfHom D₀.f (𝒰.inter s)
      σ s ((1 : (ResidueField B)) ⊗ₜ[B] x) =
        ((pullback D₀.f (specMap B (ResidueField B))).presheaf.map (homOfLE (𝒰.baseChange_inter_le D₀.f (ResidueField B) s)).op).hom
          (((pullback.fst D₀.f (specMap B (ResidueField B))).app (𝒰.inter s)).hom x))
    (hσ₂ : ∀ (s : 𝒰.Idx 1) (a : (ResidueField B)),
      letI := algebraOfHom D₀.f (𝒰.inter s)
      letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).inter s)
      σ s (a ⊗ₜ[B] (1 : Γ(D₀.A, 𝒰.inter s))) = algebraMap (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s) a)
    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation f₁ L₁ B) (hD : D₀.IsRegluingBy 𝒰 τ D)
    (c : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))))
    (hτ : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = c.1 a ξ s) :
    ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1 (c.1 a ξ) = 0 := by sorry
