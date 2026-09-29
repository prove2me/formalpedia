-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isTangentCoordsOfPairAt_local_lifts_factor_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_isTangentCoordsOfPairAt_local_lifts_factor_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/eeea7b86-a97b-5d53-8206-3ee121d1a208
-- title:
--   Tangent coordinates for a pair of local lifts
-- statement:
--   Let $B$ be an Artinian local ring with residue field $\kappa$, let $B_1$ be a $B$-algebra whose structure map $B \to B_1$ is surjective with kernel $I$ satisfying $I \cdot \mathfrak m_B = \bot$ and $I \le \mathfrak m_B$, and let $f_1 : A_1 \to \operatorname{Spec} B_1$ carry a relative group law $L_1$ over $B_1$ (a functorial multiplication, unit and inverse on points over $\operatorname{Spec} B_1$, with the group axioms and naturality). Let $V$ be a finite-dimensional $\kappa$-vector space, also a $B$-module through $\kappa$ with a central right $\kappa$-action, and $\iota : V \to B$ an injective $B$-linear map whose image is $I$. Let $D_0$ be a bare deformation of $(f_1, L_1)$ over $B$, i.e. a scheme $D_0.A$ with structure morphism $D_0.f$ to $\operatorname{Spec} B$, a commutative relative group law $D_0.L$, a property bundle, and a morphism $D_0.g : A_1 \to D_0.A$ making $f_1$ cartesian over $D_0.f$ along $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ and compatible with the group laws; assume $D_0.f$ separated. Let $\mathcal U$ be a finite ordered affine open cover of $D_0.A$, $i_0$ an index, $e_1$ a $\kappa$-point of the $i_0$-th chart of the cover obtained from $\mathcal U$ on $X_\kappa := D_0.A \times_{\operatorname{Spec} B} \operatorname{Spec}\kappa$ by pulling back along $\mathrm{pr}_1$, whose composite with the open immersion is the unit of the base-changed group law $L_\kappa :=$ `RelativeGroupLaw.baseChange` of $D_0.L$ at the identity, and assume that chart affine. Let $\varphi_1 : A_1 \to A_1$ be a morphism (no compatibility with $L_1$ assumed) and $j_\kappa : X_\kappa \to A_1$ satisfy $j_\kappa$ followed by $D_0.g$ equal to $\mathrm{pr}_1$. Let $m_i : U_i \to D_0.A$ be morphisms over $D_0.f$ whose restrictions along $D_0.g$ agree with $\varphi_1$ followed by $D_0.g$; let $D$ be a second bare deformation of $(f_1, L_1)$ over $B$, let $\iota_{D,i} : U_i \to D.A$ be morphisms over $D_0.f$ whose restrictions along $D_0.g$ agree with $D.g$, and let $m'_i : U_i \to D.A$ be morphisms over $D_0.f$ whose restrictions along $D_0.g$ agree with $\varphi_1$ followed by $D.g$. Finally let $i, j$ be indices, $W \le U_j$ an affine open of $D_0.A$, and $n, n' : W \to U_i$ with $n$ followed by the inclusion of $U_i$ equal to $m_j$ restricted to $W$, and $n'$ followed by $\iota_{D,i}$ equal to $m'_j$ restricted to $W$. Writing $C := \Gamma(D_0.A, W)$ with its $B$-algebra structure from $D_0.f$, and giving $\Gamma(X_\kappa, U_{i_0,\kappa})$ its $\kappa$-algebra structure from $\mathrm{pr}_2$, the conclusion asserts the existence of a map $e_s$ from $\Gamma(X_\kappa, U_{i_0,\kappa})$ to the $\kappa$-linear maps $\operatorname{Hom}_\kappa(V^\vee, \kappa \otimes_B C)$ which is a system of tangent coordinates of the pair at the chart $U_{i_0,\kappa}$ for the data $(I, V, \iota, C)$, the two $\operatorname{Spec} C$-points of $D.A$ obtained from $n$ and from $n'$ by composing $\mathrm{iso}_W^{-1}$ with $\iota_{D,i}$, the special fibre map $\mathrm{pr}_2$, the group law $L_\kappa$, and the reading $j_\kappa$ followed by $D.g$; that is, there are a morphism $w_0$ from $\operatorname{Spec}$ of the thickening of $C$ by $V$ into $X_\kappa$ lying over `RelTangentPoints.base`, and a lift $w_1$ of the `RelTangentPoints.translate` of $w_0$ into the chart, such that `IsTangentOfPair` holds for $I$, $V$, $\iota$, $C$, the two points and $w_0$ followed by $j_\kappa \gg D.g$, and $e_s$ is the associated `tangentCoords` of the chart ring homomorphism of $w_1$.
--
--   This is the local input to the obstruction calculus for lifting the endomorphism $\varphi_1$ across the small extension $B \to B_1$: on each affine piece $W$ of the cover it produces canonical tangent coordinates measuring the difference between the lift of $\varphi_1$ to $D$ and the lift to $D_0$ transported into $D$ along the re-gluing immersion. It is deduced from the general existence statement [`AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAt`](thm.html#AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAt) together with the cartesian description of affine charts of a nilpotent thickening, and is used by the two statements computing the obstruction cocycle of the pair.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_isTangentCoordsOfPairAt_local_lifts_factor_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_isTangentCoordsOfPairAt_local_lifts_factor_bare
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
    (e₁ : Spec (CommRingCat.of (ResidueField B)) ⟶ (((𝒰.baseChange D₀.f (ResidueField B)).U i₀) : Scheme.{0}))
    (he₁ : e₁ ≫ ((𝒰.baseChange D₀.f (ResidueField B)).U i₀).ι = ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).one (𝟙 _)).1)
    (hU : IsAffineOpen ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))

    (φ₁ : A₁ ⟶ A₁)
    (jκ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ A₁) (hjκ : jκ ≫ D₀.g = (pullback.fst D₀.f (specMap B (ResidueField B))))

    (m : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmf : ∀ i, m i ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f)
    (hmμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ m i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D₀.g)

    (D : BareDeformation f₁ L₁ B)
    (ιD : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A)
    (hιf : ∀ i, ιD i ≫ D.f = (𝒰.U i).ι ≫ D₀.f)
    (hιg : ∀ i, (D₀.g ∣_ 𝒰.U i) ≫ ιD i = (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ D.g)

    (mp : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A)
    (hmpf : ∀ i, mp i ≫ D.f = (𝒰.U i).ι ≫ D₀.f)
    (hmpμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ mp i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D.g)

    (i j : 𝒰.ι) (W : D₀.A.Opens) (hW : IsAffineOpen W) (hWj : W ≤ 𝒰.U j)
    (nn nn' : (↑W : Scheme.{0}) ⟶ ↑(𝒰.U i))
    (hnn : nn ≫ (𝒰.U i).ι = D₀.A.homOfLE hWj ≫ m j)
    (hnn' : nn' ≫ ιD i = D₀.A.homOfLE hWj ≫ mp j) :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
    letI := algebraOfHom D₀.f W
    ∃ es : Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).U i₀) →
        (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, W))),
      AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, W)
        (hW.isoSpec.inv ≫ nn ≫ ιD i) (hW.isoSpec.inv ≫ nn' ≫ ιD i)
        (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) es := by sorry
