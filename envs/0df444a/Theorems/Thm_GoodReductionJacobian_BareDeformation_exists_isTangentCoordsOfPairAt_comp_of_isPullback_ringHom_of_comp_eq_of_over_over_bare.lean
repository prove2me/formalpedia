-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isTangentCoordsOfPairAt_comp_of_isPullback_ringHom_of_comp_eq_of_over_over_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_isTangentCoordsOfPairAt_comp_of_isPullback_ringHom_of_comp_eq_of_over_over_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/8cd230b0-40dc-5244-a419-a4cf6f59bffc
-- title:
--   Functoriality of tangent coordinates under a semilinear self-base-change
-- statement:
--   Let $B$ be an artinian local ring with algebraically closed residue field $\kappa$, let $B_1$ be a $B$-algebra whose structure map is surjective with nilpotent kernel $J$ satisfying $J\cdot\mathfrak m_B=0$ and $J\subseteq\mathfrak m_B$, let $f_1:A_1\to\operatorname{Spec}B_1$ carry a commutative relative group law $L_1$ together with the bundle of properties (smooth, proper, connected fibres, a group law exists), let $V$ be a finite-dimensional $\kappa$-module which is also a $B$-module compatibly, and let $\iota:V\to B$ be an injective $B$-linear map whose image is exactly $J$. Let $D_0$ be a bare deformation of $(f_1,L_1)$ over $B$ — a scheme $D_0.A$ with $D_0.f$ to $\operatorname{Spec}B$, a commutative relative group law $D_0.L$ with the same property bundle, and a map $D_0.g$ making $A_1$ the base change along $B\to B_1$, compatibly with the group laws — with $D_0.f$ separated. Let $\mathcal U$ be an ordered affine cover of $D_0.A$, $i_0$ an index, $e_0$ a factorisation of the unit section of $D_0.L$ through $\mathcal U.U\,i_0$ and $e_1$ a factorisation of the unit section of the $\kappa$-base-changed group law through the $i_0$-th member of the base-changed cover; for every pair $s$ of indices let $\sigma_s$ be the canonical ring isomorphism $\kappa\otimes_B\Gamma(D_0.A,\mathcal U.\mathrm{inter}\,s)\cong\Gamma(\text{pullback},(\mathcal U.\mathrm{baseChange})\,\mathrm{inter}\,s)$, characterised by its values on $1\otimes x$ and on $a\otimes 1$. Let $\varphi:B\to B$ be a ring endomorphism inducing the identity on $B_1$, let $\varphi_V:V\to V$ be $\kappa$-linear with $\iota\circ\varphi_V=\varphi\circ\iota$, and let $k_0$ be an endomorphism of $D_0.A$ making it cartesian over $\operatorname{Spec}\varphi$, fixing $D_0.g$ and fixing the first projection of the base change to $\kappa$. Fix a pair $s$, an endomorphism $k_{0,s}$ of the overlap $\mathcal U.\mathrm{inter}\,s$ lifting $k_0$, and self-isomorphisms $\tau_s,\tau_s'$ of that overlap, both over $\operatorname{Spec}B$, with $\tau_s'$ followed by $k_{0,s}$ equal to $k_{0,s}$ followed by $\tau_s$. Assume $c_s$ is a system of tangent coordinates for the pair consisting of the canonical map from the spectrum of $\Gamma(D_0.A,\mathcal U.\mathrm{inter}\,s)$ and its composite with $\tau_s$, in the sense of `IsTangentCoordsOfPairAt` for the ideal $J$, the module $V$ and $\iota$: there are a map $w_0$ from the spectrum of the thickening $(\kappa\otimes_B\Gamma)\otimes_\kappa(\kappa\oplus V)$ to the base change of $D_0.A$ lying over the tangent base, and a lift $w_1$ into the chosen open, such that $w_0$ followed by the first projection is a tangent vector of that pair, $w_1$ followed by the open immersion is the translate of $w_0$ to the unit section, and $c_s$ is the associated `tangentCoords`. The conclusion is that there exists $c_s'$ satisfying the same predicate with $\tau_s'$ in place of $\tau_s$, and such that $\sigma_s(c_s'(a)(\xi))=\sigma_s(c_s(a)(\xi\circ\varphi_V))$ for all sections $a$ over the base-changed open and all $\xi$ in the $\kappa$-dual of $V$.
--
--   This is the equivariance of canonical tangent coordinates under the self-base-change $k_0$ of a bare deformation along a ring endomorphism $\varphi$ of $B$ that is the identity modulo $J$: transporting the overlap automorphism $\tau_s$ to its $k_0$-pullback $\tau_s'$ replaces the tangent coordinates by their precomposition with $\varphi_V$ on the dual side. It is used in the construction of a regluing datum with prescribed tangent coordinates, in [`GoodReductionJacobian.BareDeformation.exists_isRegluingBy_isTangentCoordsOfPairAt_comp_of_isPullback_ringHom_bare`](thm.html#GoodReductionJacobian.BareDeformation.exists_isRegluingBy_isTangentCoordsOfPairAt_comp_of_isPullback_ringHom_bare).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_isTangentCoordsOfPairAt_comp_of_isPullback_ringHom_of_comp_eq_of_over_over_bare.lean

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
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing Scheme.TwoAffineOpenCover
open scoped Quaternion TensorProduct NumberField

theorem GoodReductionJacobian.BareDeformation.exists_isTangentCoordsOfPairAt_comp_of_isPullback_ringHom_of_comp_eq_of_over_over_bare
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

    (φ : B →+* B) (hφ₁ : (algebraMap B B₁).comp φ = algebraMap B B₁)
    (φV : V →ₗ[(ResidueField B)] V) (hφV : ∀ v : V, ι (φV v) = φ (ι v))
    (k₀ : D₀.A ⟶ D₀.A) (hk₀c : CategoryTheory.IsPullback k₀ D₀.f D₀.f (Spec.map (CommRingCat.ofHom φ)))
    (hk₀g : D₀.g ≫ k₀ = D₀.g) (hk₀κ : (pullback.fst D₀.f (specMap B (ResidueField B))) ≫ k₀ = (pullback.fst D₀.f (specMap B (ResidueField B))))

    (s : 𝒰.Idx 1) (k₀s : (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑(𝒰.inter s)) (hk₀s : k₀s ≫ (𝒰.inter s).ι = (𝒰.inter s).ι ≫ k₀)
    (τs τs' : ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (hτB : τs.hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f) (hτ'B : τs'.hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f)
    (hττ' : τs'.hom ≫ k₀s = k₀s ≫ τs.hom)

    (cs : letI := algebraOfHom D₀.f (𝒰.inter s)
      Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))))
    (hcs : letI := algebraOfHom D₀.f (𝒰.inter s)
      AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ τs.hom ≫ (𝒰.inter s).ι)
        (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs) :
    letI := algebraOfHom D₀.f (𝒰.inter s)
    ∃ cs' : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
      AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ τs'.hom ≫ (𝒰.inter s).ι)
        (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs' ∧
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs' a ξ) = σ s (cs a (ξ ∘ₗ φV)) := by sorry
