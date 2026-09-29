-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_isTangentCoordsOfPairAt_comp_regluing_chart_of_comp_incl_bare
-- name    : GoodReductionJacobian.BareDeformation.isTangentCoordsOfPairAt_comp_regluing_chart_of_comp_incl_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/5f58ac29-c315-568c-88e3-5ef4b7e58bc0
-- title:
--   Tangent coordinates of a pair transported through a regluing chart
-- statement:
--   Let $B$ be a commutative local Artinian ring and $B_1$ a commutative $B$-algebra, and put $I := \ker(B \to B_1)$; assume $I \cdot \mathfrak m_B = 0$ and $I \subseteq \mathfrak m_B$. Let $f_1 : A_1 \to \operatorname{Spec} B_1$ carry a relative group law $L_1$. Let $V$ be an abelian group with commuting module structures over $B$ and over the residue field $\kappa =$ `ResidueField B` (compatible via a scalar tower, with a central right $\kappa$-action), and $\iota : V \to B$ a $B$-linear map. Let $D_0$ and $D$ be bare deformations of $(f_1,L_1)$ over $B$: schemes with structure map to $\operatorname{Spec} B$, commutative relative group law, the property bundle of an abelian scheme, and comparison maps $D_0.g, D.g$ from $A_1$ that are cartesian over $B \to B_1$ and compatible with the group laws. Let $\mathcal U$ be an ordered affine cover of $D_0.A$ (a finite linearly ordered family of affine opens covering it), $i_0$ and $k$ indices. Write $X_\kappa$ for the pullback of $D_0.f$ along $\operatorname{Spec}\kappa \to \operatorname{Spec} B$, with projections $\mathrm{pr}_1,\mathrm{pr}_2$ and the base-changed group law $L_\kappa$ of $D_0.L$. Assume given $j_\kappa : X_\kappa \to A_1$ with $j_\kappa$ followed by $D_0.g$ equal to $\mathrm{pr}_1$, and $\iota_k : \mathcal U_k \to D.A$ with $(D_0.g\mid_{\mathcal U_k})$ followed by $\iota_k$ equal to the inclusion of $D_0.g^{-1}\mathcal U_k$ followed by $D.g$. Let $C$ be a $B$-algebra, $x,y : \operatorname{Spec} C \to \mathcal U_k$ two $C$-points, and $c$ a map from $\Gamma(X_\kappa, \mathcal U_{i_0,\kappa})$, the sections over the preimage open $\mathrm{pr}_1^{-1}\mathcal U_{i_0}$, to $\kappa$-linear maps $\operatorname{Hom}_\kappa(V,\kappa) \to \kappa \otimes_B C$. The assertion: if $c$ is a system of tangent coordinates at $\mathcal U_{i_0,\kappa}$ for the pair $(x,y)$ pushed into $D_0.A$ along the open inclusion $\mathcal U_k \hookrightarrow D_0.A$, relative to the data $(\mathrm{pr}_2, L_\kappa, \mathrm{pr}_1)$ — that is, there are a point of $X_\kappa$ with values in the thickening of $C$ by $V$ lying over the canonical $\kappa$-base point, a lift of its $L_\kappa$-translate into the open $\mathcal U_{i_0,\kappa}$, the pair condition `IsTangentOfPair` for $I, V, \iota, C$, and $c$ equal to the resulting chart tangent coordinates — then the same holds for the pair $(x,y)$ pushed into $D.A$ along $\iota_k$, with the comparison map $\mathrm{pr}_1$ replaced by $j_\kappa$ followed by $D.g$, with the same $c$.
--
--   This is the invariance of canonical tangent coordinates under a regluing chart: the coordinates read off on the unit chart $\mathcal U_{i_0,\kappa}$ of the special fibre do not change when a pair of $C$-points of a chart $\mathcal U_k$ of the first deformation is transported into a second deformation along a chart map $\iota_k$ compatible with the two comparison maps from $A_1$. It feeds the construction of the endomorphism obstruction cocycle for bare deformations and the statements that compute that cocycle's difference under regluing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_isTangentCoordsOfPairAt_comp_regluing_chart_of_comp_incl_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.isTangentCoordsOfPairAt_comp_regluing_chart_of_comp_incl_bare
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    [CommRing B₁] [Algebra B B₁]
    (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥)
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    [Module (ResidueField B)ᵐᵒᵖ V] [IsCentralScalar (ResidueField B) V]
    (ι : V →ₗ[B] B)
    (D₀ : BareDeformation f₁ L₁ B) (𝒰 : D₀.A.OrderedAffineCover) (i₀ : 𝒰.ι)

    (jκ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ A₁) (hjκ : jκ ≫ D₀.g = (pullback.fst D₀.f (specMap B (ResidueField B))))

    (D : BareDeformation f₁ L₁ B) (k : 𝒰.ι)
    (ιDk : (↑(𝒰.U k) : Scheme.{0}) ⟶ D.A)
    (hιg : (D₀.g ∣_ 𝒰.U k) ≫ ιDk = (D₀.g ⁻¹ᵁ 𝒰.U k).ι ≫ D.g)

    (C : Type) [CommRing C] [Algebra B C]
    (x y : Spec (CommRingCat.of C) ⟶ ↑(𝒰.U k))
    (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] C)))
    (hc : AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι C (x ≫ (𝒰.U k).ι) (y ≫ (𝒰.U k).ι)
      (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) c) :
    AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι C (x ≫ ιDk) (y ≫ ιDk)
      (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) c := by sorry
