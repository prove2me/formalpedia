-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isTangentCoordsOfPairAt_comp_local_lifts_factor_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_isTangentCoordsOfPairAt_comp_local_lifts_factor_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/7ecdf452-f420-5d9c-8b76-7e9c36d93d1c
-- title:
--   Tangent coordinates comparing a composite lift with a factored lift
-- statement:
--   Fix a local Artinian commutative ring $B$ with residue field $\kappa = \mathrm{ResidueField}\,B$ and a commutative $B$-algebra $B_1$ whose structure map is surjective with kernel $I$ satisfying $I\cdot\mathfrak m_B = 0$ and $I \subseteq \mathfrak m_B$; fix a scheme $A_1$ with $f_1 : A_1 \to \operatorname{Spec} B_1$ and a relative group law $L_1$ on $f_1$ (unital, associative, with inverses, natural in the test base), and a finite-dimensional $\kappa$-vector space $V$, also a $B$-module with compatible central right $\kappa$-action, together with an injective $B$-linear $\iota : V \to B$ whose image is exactly $I$. Let $D_0$ be a `BareDeformation` of $(f_1,L_1)$ over $B$: a scheme $D_0.A$ with a structure morphism $D_0.f$ carrying a commutative relative group law $D_0.L$ and an abelian-scheme property bundle, together with $D_0.g : A_1 \to D_0.A$ making a cartesian square over $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ and compatible with the group laws; assume $D_0.f$ separated. Let $\mathcal U$ be an ordered affine cover of $D_0.A$ (a finite linearly ordered family of affine opens covering it), $i_0$ an index, and let $e_1 : \operatorname{Spec}\kappa \to U_{i_0,\kappa}$ be a section of the $i_0$-th member of the cover $\mathcal U$ base changed along $\operatorname{Spec}\kappa \to \operatorname{Spec} B$ (the preimage cover of $\operatorname{pr}_1$) whose composite with the open immersion is the unit of the base-changed group law, with $U_{i_0,\kappa}$ affine. Let $\varphi_1,\varphi_1',\varphi_1'' : A_1 \to A_1$ with $\varphi_1''$ equal to $\varphi_1'$ followed by $\varphi_1$, and let $m_i, m_i', m_i'' : U_i \to D_0.A$ be families of morphisms over $\operatorname{Spec} B$ (each $m_i \circ$-composed with $D_0.f$ agreeing with the inclusion followed by $D_0.f$) lifting $\varphi_1,\varphi_1',\varphi_1''$ in the sense that on $D_0.g^{-1}(U_i)$ the restriction of $D_0.g$ followed by the local lift agrees with the inclusion followed by the relevant endomorphism followed by $D_0.g$. Finally fix indices $i,j$, an affine open $W \subseteq U_j$ and $n : W \to U_i$ with $n$ followed by the inclusion of $U_i$ equal to the inclusion $W \subseteq U_j$ followed by $m_j'$. Then, writing $C = \Gamma(D_0.A, W)$ with its $B$-algebra structure coming from $D_0.f$, there exists a function $es$ from $\Gamma$ of the base-changed chart $U_{i_0,\kappa}$ to $\kappa$-linear maps $V^\vee \to \kappa \otimes_B C$ which is a system of tangent coordinates at the unit chart for the pair of morphisms $\operatorname{Spec} C \to D_0.A$ given by $n$ followed by $m_i$ and by the inclusion $W \subseteq U_j$ followed by $m_j''$ (both read through the inverse of the canonical isomorphism $\operatorname{Spec} C \cong W$), relative to $\operatorname{pr}_2$, the base-changed group law and $\operatorname{pr}_1$ on $D_0.A \times_{\operatorname{Spec} B} \operatorname{Spec}\kappa$: that is, there are a point $w_0$ of the special fibre with values in the thickening of $C$ by $V$ lying over the canonical base point, and a lift $w_1$ into the chart $U_{i_0,\kappa}$ of the translate of $w_0$ by the group law, such that the pair of the two morphisms is tangent along $w_0$ followed by $\operatorname{pr}_1$ in the sense of `IsTangentOfPair` for $I$, $V$, $\iota$, $C$, and $es$ is the tangent-coordinate function attached to the chart ring homomorphism of $w_1$.
--
--   This is the existence step in the deformation-theoretic comparison of two lifts of one endomorphism along a small extension $B \to B_1$: the difference between the composite's own local lift $m_j''$ and the composite of lifts $n$ followed by $m_i$ is measured by a $V$-valued tangent vector, and the statement produces the coordinates of that difference in the chart at the unit of the special fibre. It is the input to the computation of the obstruction cocycle of a composite endomorphism, whose difference term is expressed through these coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_isTangentCoordsOfPairAt_comp_local_lifts_factor_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_isTangentCoordsOfPairAt_comp_local_lifts_factor_bare
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁))
    (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥)
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    [Module (ResidueField B)ᵐᵒᵖ V] [IsCentralScalar (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))

    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f]
    (𝒰 : D₀.A.OrderedAffineCover) (i₀ : 𝒰.ι)
    (e₁ : Spec (CommRingCat.of (ResidueField B)) ⟶ ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) : Scheme.{0}))
    (he₁ : e₁ ≫ (((𝒰.baseChange D₀.f (ResidueField B)).U i₀)).ι = ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).one (𝟙 _)).1)
    (hU : IsAffineOpen ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))

    (φ₁ φ₁' φ₁'' : A₁ ⟶ A₁) (hcomp : φ₁'' = φ₁' ≫ φ₁)

    (m : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmf : ∀ i, m i ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f)
    (hmμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ m i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D₀.g)
    (m' : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmf' : ∀ i, m' i ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f)
    (hmμ' : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ m' i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁' ≫ D₀.g)
    (m'' : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmf'' : ∀ i, m'' i ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f)
    (hmμ'' : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ m'' i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁'' ≫ D₀.g)

    (i j : 𝒰.ι) (Wo : D₀.A.Opens) (hWo : IsAffineOpen Wo) (hWj : Wo ≤ 𝒰.U j)
    (nn : (↑Wo : Scheme.{0}) ⟶ ↑(𝒰.U i))
    (hnn : nn ≫ (𝒰.U i).ι = D₀.A.homOfLE hWj ≫ m' j) :
    letI := algebraOfHom D₀.f Wo
    ∃ es : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, Wo))),
      AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, Wo)
        (hWo.isoSpec.inv ≫ nn ≫ m i) (hWo.isoSpec.inv ≫ D₀.A.homOfLE hWj ≫ m'' j)
        (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) es := by sorry
