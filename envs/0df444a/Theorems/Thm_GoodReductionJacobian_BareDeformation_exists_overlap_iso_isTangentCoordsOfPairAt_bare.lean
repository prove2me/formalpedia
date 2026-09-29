-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_overlap_iso_isTangentCoordsOfPairAt_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_overlap_iso_isTangentCoordsOfPairAt_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/48b53edb-9e8c-5860-8db8-5d6a3fed1e76
-- title:
--   Overlap automorphism realising a tangent cocycle component
-- statement:
--   Let $B$ be an Artinian local ring with algebraically closed residue field $k=\mathrm{ResidueField}\,B$, let $B_1$ be a $B$-algebra with $B\to B_1$ surjective, put $J=\ker(B\to B_1)$, and assume $J$ is nilpotent, $J\cdot\mathfrak m_B=0$ and $J\subseteq\mathfrak m_B$. Let $f_1:A_1\to\operatorname{Spec}B_1$ carry a commutative relative group law $L_1$ together with the bundle of properties (smooth, proper, connected fibres, a group law exists). Let $V$ be a finite-dimensional $k$-vector space, also a $B$-module compatibly, with central right $k$-action, and let $\iota:V\to B$ be an injective $B$-linear map with image $J$. Let $D_0$ be a bare deformation of $(f_1,L_1)$ to $B$: a scheme $D_0.A$ with separated structure map $D_0.f$ to $\operatorname{Spec}B$, a commutative relative group law $D_0.L$ with the same property bundle, and $D_0.g:A_1\to D_0.A$ making a pullback square over $\operatorname{Spec}B_1\to\operatorname{Spec}B$ and compatible with multiplication. Let $\mathcal U$ be a finite ordered affine cover of $D_0.A$, $i_0$ an index, $e_0$ a factorisation of the unit section of $D_0.L$ through $\mathcal U.U\,i_0$, and $e_1$ a factorisation of the unit section of the group law base-changed along $\operatorname{Spec}k\to\operatorname{Spec}B$ through the corresponding chart of the base-changed cover. For each overlap index $s\in\mathcal U.\mathrm{Idx}\,1$ (a strictly monotone pair of indices, with $\mathcal U.\mathrm{inter}\,s$ the intersection of the two charts) let $\sigma_s$ be a ring isomorphism $k\otimes_B\Gamma(D_0.A,\mathcal U.\mathrm{inter}\,s)\cong\Gamma(A_k,(\mathcal U_k).\mathrm{inter}\,s)$, where $A_k$ is the pullback of $D_0.f$ along $\operatorname{Spec}k\to\operatorname{Spec}B$, subject to $\sigma_s(1\otimes x)$ being the restriction of the pullback of $x$ and $\sigma_s(a\otimes 1)$ being the image of $a$ under the structure map. Let $c$ be a $k$-linear point derivation of $\Gamma(A_k,(\mathcal U_k).U\,i_0)$ at the point $e_1$, with values in $\operatorname{Hom}_k(V^\vee,\check C^1(\mathcal U_k,\mathcal O))$ for the unit $\mathcal O$-module presheaf, and assume each $c(a)(\xi)$ lies in the kernel of the first Čech differential. Then for every $s$ there is an isomorphism $\tau_s$ of $\mathcal U.\mathrm{inter}\,s$ with itself over $\operatorname{Spec}B$ (that is, $\tau_s$ followed by the open immersion and $D_0.f$ equals the open immersion followed by $D_0.f$) which fixes the restriction of $D_0.g$ to that overlap, and a map $c_s:\Gamma(A_k,(\mathcal U_k).U\,i_0)\to\operatorname{Hom}_k(V^\vee,k\otimes_B\Gamma(D_0.A,\mathcal U.\mathrm{inter}\,s))$ such that $c_s$ is a system of tangent coordinates, in the sense of `IsTangentCoordsOfPairAt` for $J$, $V$, $\iota$ and $C=\Gamma(D_0.A,\mathcal U.\mathrm{inter}\,s)$, for the pair consisting of the canonical map $\operatorname{Spec}C\to D_0.A$ of the affine overlap and the map obtained from it by inserting $\tau_s$, taken relative to the special fibre $A_k$, the base-changed group law and the chart $(\mathcal U_k).U\,i_0$; and $\sigma_s(c_s(a)(\xi))$ is the $s$-component of the cochain $c(a)(\xi)$ for all $a$ and $\xi$.
--
--   This is the first step of the re-gluing construction which produces, from a Čech $1$-cocycle of tangent data on the special fibre, an actual deformation of the abelian scheme across the small extension $B\to B_1$: on each overlap of the chosen affine cover, the prescribed cocycle component is realised by an automorphism of the overlap that is the identity modulo $J$. It is used by [`GoodReductionJacobian.BareDeformation.exists_isRegluingBy_isTangentCoordsOfPairAt_bare`](thm.html#GoodReductionJacobian.BareDeformation.exists_isRegluingBy_isTangentCoordsOfPairAt_bare), where these overlap automorphisms are assembled into regluing data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_overlap_iso_isTangentCoordsOfPairAt_bare.lean

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

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover
open AlgebraicGeometry

open scoped Quaternion TensorProduct NumberField

theorem GoodReductionJacobian.BareDeformation.exists_overlap_iso_isTangentCoordsOfPairAt_bare
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
    (c : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) (((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom
          (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)))
    (hc : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ
        ∈ LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))
    (s : 𝒰.Idx 1) :
    ∃ τs : ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)),
      τs.hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f ∧
      (D₀.g ∣_ 𝒰.inter s) ≫ τs.hom = D₀.g ∣_ 𝒰.inter s ∧
      letI := algebraOfHom D₀.f (𝒰.inter s)
      letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
        AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
          ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
          ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ τs.hom ≫ (𝒰.inter s).ι)
          (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
        ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
          σ s (cs a ξ) = (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ s := by sorry
