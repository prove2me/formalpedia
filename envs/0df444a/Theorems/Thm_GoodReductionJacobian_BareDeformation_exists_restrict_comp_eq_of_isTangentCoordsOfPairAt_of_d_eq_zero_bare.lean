-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_restrict_comp_eq_of_isTangentCoordsOfPairAt_of_d_eq_zero_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_restrict_comp_eq_of_isTangentCoordsOfPairAt_of_d_eq_zero_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/482f05e7-74fe-520d-bf4d-49dca2dca26b
-- title:
--   Triple-overlap cocycle identity for the regluing automorphisms
-- statement:
--   Let $B$ be an Artinian local ring with algebraically closed residue field $k=\mathrm{ResidueField}\,B$, let $B_1$ be a $B$-algebra whose structure map is surjective with nilpotent kernel $I$ satisfying $I\cdot\mathfrak m_B=\bot$ and $I\le\mathfrak m_B$, let $f_1:A_1\to\operatorname{Spec}B_1$ carry a commutative relative group law $L_1$ and satisfy `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, a group law exists), and let $V$ be a finite-dimensional $k$-vector space with compatible $B$-module and opposite-module structures together with an injective $B$-linear $\iota:V\to B$ whose range is $I$. Let $D_0$ be a `BareDeformation` of $(f_1,L_1)$ over $B$: a scheme $A=D_0.A$ with separated $f=D_0.f$ over $\operatorname{Spec}B$, a commutative group law $L$ with the abelian-scheme bundle, and $g:A_1\to A$ making the square over $\operatorname{Spec}B_1\to\operatorname{Spec}B$ cartesian and compatible with the group laws. Fix an ordered affine cover $\mathcal U$ of $A$ (a finite linearly ordered index set, affine opens with supremum $\top$), an index $i_0$, a section $e_0$ of $U_{i_0}$ lifting the unit point of $L$, and a section $e_1$ lifting the unit point of the base-changed group law on $\operatorname{pullback}(f,\operatorname{Spec}k\to\operatorname{Spec}B)$ into the base-changed chart. Let $\sigma_s$, for $s$ a strictly increasing pair of indices, be ring isomorphisms $k\otimes_B\Gamma(A,\mathcal U.\mathrm{inter}\,s)\cong\Gamma(\text{pullback},(\mathcal U.\mathrm{baseChange})\,\mathrm{inter}\,s)$ normalised by $1\otimes x\mapsto$ the restricted pullback of $x$ and $a\otimes 1\mapsto$ the image of $a$ under the structure map. Let $c$ be a $k$-linear map on $\Gamma$ of the base-changed chart $U_{i_0}$, with values in $\mathrm{Hom}_k(V^{*},\,C^1)$ where $C^1$ is the degree-one Čech cochain group of the unit $\mathcal O$-module presheaf for the base-changed cover, satisfying the Leibniz rule at the evaluation homomorphism determined by $e_1$, and assume every value $c(a)(\xi)$ lies in the kernel of the Čech differential $d^1$. Finally let $\tau_s$ be automorphisms of the schemes $\mathcal U.\mathrm{inter}\,s$ over $\operatorname{Spec}B$, compatible with $g$ restricted to $\mathcal U.\mathrm{inter}\,s$, and such that for each $s$ there is a coordinate family $c_s$ with $\mathrm{IsTangentCoordsOfPairAt}$ for the ideal $I$, the pair $\iota,V$ and the ring $C=\Gamma(A,\mathcal U.\mathrm{inter}\,s)$, comparing the canonical $C$-point $\mathrm{fromSpec}$ of $A$ with the $C$-point obtained from $\mathrm{isoSpec}^{-1}$ followed by $\tau_s$ and the open immersion — that is, there are a thickened point $w_0$ of the special-fibre chart over the relative tangent base and a lift $w_1$ into the base-changed chart $U_{i_0}$ equal to the $L$-translate of $w_0$ to the unit section, the two $C$-points form a tangent pair for $w_0$ followed by the first projection, and $c_s$ is the tangent-coordinate function of the ring homomorphism cut out by $w_1$ — and with $\sigma_s\circ c_s$ equal to the $s$-component of $c$. The conclusion: for every strictly increasing triple $r$ there are morphisms $\rho_0,\rho_1,\rho_2:\mathcal U.\mathrm{inter}\,r\to\mathcal U.\mathrm{inter}\,r$ such that for each $j$ the morphism $\rho_j$ followed by the inclusion $\mathcal U.\mathrm{inter}\,r\subseteq\mathcal U.\mathrm{inter}(\mathcal U.\mathrm{face}\,r\,j)$ equals that inclusion followed by $\tau_{\mathcal U.\mathrm{face}\,r\,j}$, and $\rho_1=\rho_2$ followed by $\rho_0$.
--
--   This is the cocycle step of the regluing construction: each overlap automorphism $\tau_s$, prescribed by the tangent-coordinate cochain $c$, restricts to the triple overlaps, and the cocycle condition $d^1c=0$ forces the resulting restrictions to compose as $\tau_{ik}=\tau_{ij}$ followed by $\tau_{jk}$. It is used by [`GoodReductionJacobian.BareDeformation.exists_isRegluingBy_isTangentCoordsOfPairAt_bare`](thm.html#GoodReductionJacobian.BareDeformation.exists_isRegluingBy_isTangentCoordsOfPairAt_bare), where the $\rho_j$ supply the gluing data for a lift of the bare deformation along the small extension $B\to B_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_restrict_comp_eq_of_isTangentCoordsOfPairAt_of_d_eq_zero_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_restrict_comp_eq_of_isTangentCoordsOfPairAt_of_d_eq_zero_bare
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
    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (hτB : ∀ s : 𝒰.Idx 1, (τ s).hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f)
    (hτg : ∀ s : 𝒰.Idx 1, (D₀.g ∣_ 𝒰.inter s) ≫ (τ s).hom = D₀.g ∣_ 𝒰.inter s)
    (hτc : ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
            σ s (cs a ξ) = (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ s) :
    ∀ r : 𝒰.Idx 2, ∃ ρ : Fin 3 → ((↑(𝒰.inter r) : Scheme.{0}) ⟶ ↑(𝒰.inter r)),
        (∀ j : Fin 3, ρ j ≫ D₀.A.homOfLE (𝒰.inter_le_inter_face r j)
            = D₀.A.homOfLE (𝒰.inter_le_inter_face r j) ≫ (τ (𝒰.face r j)).hom) ∧
        ρ 1 = ρ 2 ≫ ρ 0 := by sorry
