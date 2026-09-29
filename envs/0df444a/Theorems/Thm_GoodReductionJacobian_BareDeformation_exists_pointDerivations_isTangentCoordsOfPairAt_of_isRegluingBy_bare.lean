-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_pointDerivations_isTangentCoordsOfPairAt_of_isRegluingBy_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_pointDerivations_isTangentCoordsOfPairAt_of_isRegluingBy_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/b53f94dd-09c1-54d3-9110-3105d825f1ad
-- title:
--   Point-derivation tangent coordinates for the overlaps of a regluing
-- statement:
--   Let $B$ be a local artinian ring with algebraically closed residue field $\kappa =$ `ResidueField B`, let $B_1$ be a $B$-algebra whose structure map is surjective with nilpotent kernel $J$, and assume $J\cdot\mathfrak m_B = 0$ and $J \le \mathfrak m_B$. Let $V$ be a finite-dimensional $\kappa$-vector space, also a $B$-module compatibly through $\kappa$ and with central opposite action, and let $\iota : V \to B$ be an injective $B$-linear map whose image is $J$. Let $f_1 : A_1 \to \operatorname{Spec} B_1$ carry a commutative relative group law $L_1$ and satisfy the bundle `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, group law present). Let $D_0$ be a `BareDeformation` of $(f_1, L_1)$ over $B$ with separated structure morphism: a scheme $D_0.A \to \operatorname{Spec} B$ with commutative relative group law $D_0.L$, the same bundle of properties, and a morphism $D_0.g$ from $A_1$ making the square over $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ cartesian and compatible with the group laws. Let $\mathcal U$ be a finite ordered affine open cover of $D_0.A$, $i_0$ an index, $e_0 : \operatorname{Spec} B \to \mathcal U.U\,i_0$ a lift of the unit section of $D_0.L$, and $e_1$ a lift, in the cover base-changed to $\kappa$, of the unit section of the base-changed group law. Let $\sigma$ give, for each $1$-simplex $s$ of the cover (a strictly increasing pair of indices, with $\mathcal U.\mathrm{inter}\,s$ the corresponding intersection), a ring isomorphism $\kappa \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s) \cong \Gamma$ of the base-changed intersection, carrying $1 \otimes x$ to the restriction of the pullback of $x$ along the first projection and $a \otimes 1$ to the image of $a$ under the structure map. Let $\tau$ assign to each $1$-simplex $s$ a self-isomorphism of the scheme $\mathcal U.\mathrm{inter}\,s$, and let $D$ be a further bare deformation with $D_0.\mathrm{IsRegluingBy}\ \mathcal U\ \tau\ D$, i.e. each $\tau_s$ lies over $D_0.f$, is the identity after restriction along $D_0.g$, and $D$ is obtained by gluing the charts $\mathcal U.U\,i$ along the $\tau_s$ by a family of open immersions over $D_0.f$ covering $D.A$ and compatible with $D.g$. Then there is a $\kappa$-point derivation $c$ of the chart ring $\Gamma$ of the base-changed open $i_0$, at the evaluation homomorphism determined by $e_1$, with values in $\operatorname{Hom}_\kappa(V^\vee, \check C^1)$, where $\check C^1$ is the module of $1$-cochains $\prod_s \Gamma(\mathcal U_\kappa.\mathrm{inter}\,s)$ of the unit $\mathcal O$-module presheaf for the second projection, such that for every $1$-simplex $s$ there is a map $c_s$ from that chart ring to $\operatorname{Hom}_\kappa(V^\vee, \kappa \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s))$ which is a system of tangent coordinates, in the sense of `IsTangentCoordsOfPairAt` for the ideal $J$, the pair $V, \iota$ and the coefficient ring $\Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s)$, for the pair of points given by the canonical map $\mathrm{fromSpec}$ of the affine open $\mathcal U.\mathrm{inter}\,s$ and by $\mathrm{isoSpec}^{-1}$ followed by $\tau_s$ followed by the inclusion, taken relative to the base-changed structure morphism, the base-changed group law and the first projection, and such that $\sigma_s(c_s(a)(\xi))$ equals the $s$-component of $c(a)(\xi)$ for all sections $a$ and all $\xi \in V^\vee$. Here `IsTangentCoordsOfPairAt` asserts the existence of a point of $A_\kappa$ with values in the thickening $(\kappa \otimes_B \Gamma) \otimes_\kappa (\kappa \oplus V)$ lying over the relative tangent base, whose composite with the first projection exhibits it as a tangent vector of the given pair of points, together with a lift into the chosen open of its group-law translate to the unit section, the coordinates $c_s$ being those read off from the resulting chart homomorphism.
--
--   This is the overlap step in the Schlessinger-style infinitesimal analysis of deformations of an abelian scheme along a small extension $B \to B_1$: the automorphisms $\tau_s$ used to reglue $D_0$ into $D$ are measured by tangent coordinates which, after transport through the comparison isomorphisms $\sigma_s$, assemble into a single point-derivation-valued Čech $1$-cochain. It is used by [`GoodReductionJacobian.BareDeformation.exists_isRegluingBy_exists_isTangentCoordsOfPairAt_of_bareDeformation_bare`](thm.html#GoodReductionJacobian.BareDeformation.exists_isRegluingBy_exists_isTangentCoordsOfPairAt_of_bareDeformation_bare), where an arbitrary deformation is first exhibited as a regluing of a fixed one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_pointDerivations_isTangentCoordsOfPairAt_of_isRegluingBy_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_pointDerivations_isTangentCoordsOfPairAt_of_isRegluingBy_bare
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
    (D : BareDeformation f₁ L₁ B) (hD : D₀.IsRegluingBy 𝒰 τ D) :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
    ∃ c : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))),
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = c.1 a ξ s := by sorry
