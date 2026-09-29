-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_isTangentOfPair_specMap_comp_of_isPullback_ringHom_of_comp_eq_bare
-- name    : GoodReductionJacobian.BareDeformation.isTangentOfPair_specMap_comp_of_isPullback_ringHom_of_comp_eq_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/22273c1b-32b6-5a0c-8a43-3790dea1bcca
-- title:
--   Pair tangent field transported by a cartesian self-map
-- statement:
--   Fix a commutative Artinian local ring $B$ with algebraically closed residue field $\kappa = \mathrm{ResidueField}\,B$ and a $B$-algebra $B_1$ whose structure map is surjective with nilpotent kernel $J$ satisfying $J\cdot\mathfrak m_B = 0$ and $J \subseteq \mathfrak m_B$; fix a scheme $A_1$ over $\operatorname{Spec} B_1$ with a commutative relative group law $L_1$ and the bundle of properties (smooth, proper, connected fibres, a group law exists); fix a finite-dimensional $\kappa$-vector space $V$, also a $B$-module compatibly and with central right $\kappa$-action, and an injective $B$-linear $\iota : V \to B$ with image $J$. Let $D_0$ be a bare deformation of $(f_1, L_1)$ to $B$ (a scheme $D_0.A$ with a structure map $D_0.f$, a commutative relative group law, the abelian-scheme property bundle, and a map $D_0.g$ from $A_1$ cartesian over $\operatorname{Spec}(B \to B_1)$ and compatible with the group laws), with $D_0.f$ separated, together with an ordered affine cover $\mathcal U$ of $D_0.A$, an index $i_0$ and sections $e_0$ over $B$ and $e_1$ over $\kappa$ of the identity points of $D_0.L$ and of its base change, and, for each overlap index $s$, ring isomorphisms $\sigma_s : \kappa \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s) \to \Gamma$ of the corresponding open of the base-changed cover, normalised on $1 \otimes x$ by the first projection of the pullback and on $a \otimes 1$ by the structure map. Let $\varphi$ be a ring endomorphism of $B$ over $B_1$, let $\varphi_V$ be $\kappa$-linear on $V$ with $\iota \circ \varphi_V = \varphi \circ \iota$, and let $k_0$ be a self-map of $D_0.A$ making the square with $D_0.f$, $D_0.f$ and $\operatorname{Spec}\varphi$ cartesian, fixing $D_0.g$ and the first projection to the special fibre. Fix an overlap index $s$, write $C = \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s)$ with its $B$-algebra structure from $D_0.f$, let $k_{0,s}$ be a self-map of the overlap lying over $k_0$, and let $\tau_s, \tau_s'$ be automorphisms of the overlap over $\operatorname{Spec} B$ with $\tau_s' \text{ followed by } k_{0,s} = k_{0,s} \text{ followed by } \tau_s$. Finally let $w_0 : \operatorname{Spec}\bigl((\kappa \otimes_B C) \otimes_\kappa (\kappa \oplus V)\bigr) \to D_0.A \times_{\operatorname{Spec} B} \operatorname{Spec} \kappa$ be such that $w_0$ followed by the first projection is a tangent map of the pair consisting of the canonical $\operatorname{Spec} C \to D_0.A$ and of its composite with $\tau_s$: that is, there are a ring map $\vartheta$ from the pair ring $\{(a,b) \in C \times C : a \equiv b \bmod JC\}$ to the thickening satisfying the two Schlessinger normalisations ($\vartheta(a,a) = \bar a \otimes 1$, and $\vartheta(0, \iota(v)c) = \bar c \otimes \mathrm{inr}(v)$) and a map from $\operatorname{Spec}$ of the pair ring to $D_0.A$ restricting along the two projections to the two given points and reproducing the given map along $\operatorname{Spec}\vartheta$. The conclusion asserts the same tangency statement for the pair consisting of the canonical point and its composite with $\tau_s'$, with the thickening map obtained from $w_0$ by precomposition with $\operatorname{Spec}$ of the identity on $\kappa \otimes_B C$ tensored with the square-zero extension map induced by $\varphi_V$, followed by the first projection.
--
--   This is the functoriality, under a cartesian self-map of the base deformation that is the identity on the special fibre, of the Schlessinger-style tangent map attached to a pair of lifts agreeing modulo the small ideal $J$. It feeds the existence statement for compatible tangent coordinates of such pairs, [`GoodReductionJacobian.BareDeformation.exists_isTangentCoordsOfPairAt_comp_of_isPullback_ringHom_of_comp_eq_of_over_over_bare`](thm.html#GoodReductionJacobian.BareDeformation.exists_isTangentCoordsOfPairAt_comp_of_isPullback_ringHom_of_comp_eq_of_over_over_bare).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_isTangentOfPair_specMap_comp_of_isPullback_ringHom_of_comp_eq_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.isTangentOfPair_specMap_comp_of_isPullback_ringHom_of_comp_eq_bare
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

    (w₀ : letI := algebraOfHom D₀.f (𝒰.inter s)
      Spec (CommRingCat.of (AlgebraicGeometry.SmallExtension.thickening B V Γ(D₀.A, 𝒰.inter s))) ⟶ (pullback D₀.f (specMap B (ResidueField B))))
    (hw : letI := algebraOfHom D₀.f (𝒰.inter s)
      AlgebraicGeometry.SmallExtension.IsTangentOfPair (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ τs.hom ≫ (𝒰.inter s).ι)
        (w₀ ≫ pullback.fst D₀.f (specMap B (ResidueField B)))) :
    letI := algebraOfHom D₀.f (𝒰.inter s)
    AlgebraicGeometry.SmallExtension.IsTangentOfPair (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
      ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
      ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ τs'.hom ≫ (𝒰.inter s).ι)
      ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))) (TrivSqZeroExt.map (R' := (ResidueField B)) φV)).toRingHom) ≫ w₀) ≫
        pullback.fst D₀.f (specMap B (ResidueField B))) := by sorry
