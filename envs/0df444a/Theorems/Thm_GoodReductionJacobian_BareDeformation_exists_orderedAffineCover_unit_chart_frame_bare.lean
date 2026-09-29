-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_orderedAffineCover_unit_chart_frame_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_orderedAffineCover_unit_chart_frame_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/3d2533e3-6d73-5629-9ddd-228d3becb6f6
-- title:
--   Affine frame for a bare deformation and its residue fibre
-- statement:
--   Let $B$ be a commutative local ring, $B_1$ a commutative $B$-algebra, $f_1 : A_1 \to \operatorname{Spec} B_1$ a morphism of schemes equipped with a relative group law $L_1$ over $B_1$, and let $D_0$ be a bare deformation of $(f_1, L_1)$ to $B$: that is, a scheme $D_0.A$ with a structure morphism $D_0.f : D_0.A \to \operatorname{Spec} B$, a commutative relative group law $D_0.L$ over $B$, an abelian-scheme property bundle for $D_0.f$ (smooth, proper, connected fibres, a group law exists), and a morphism $A_1 \to D_0.A$ making $f_1$ the base change of $D_0.f$ along $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ and compatible with the two multiplications; assume $D_0.f$ separated. Write $\kappa = \mathrm{ResidueField}\,B$. Then there exist: an ordered affine cover $\mathcal U$ of $D_0.A$ (a finite linearly ordered family of affine opens with supremum $\top$) and an index $i_0$; a morphism $e_0 : \operatorname{Spec} B \to \mathcal U.U\,i_0$ whose composite with the open immersion $(\mathcal U.U\,i_0).\iota$ is the underlying morphism of the unit $D_0.L.\mathrm{one}(\mathbb 1)$; a morphism $e_1 : \operatorname{Spec} \kappa \to (\mathcal U.\mathrm{baseChange}\,D_0.f\,\kappa).U\,i_0$, the chart of the cover of $\operatorname{pullback} D_0.f\,(\mathrm{specMap}\,B\,\kappa)$ obtained by pulling back $\mathcal U.U\,i_0$ along the first projection, whose composite with that chart's open immersion is the unit of the base-changed group law $\mathrm{RelativeGroupLaw.baseChange}\,(\mathrm{specMap}\,B\,\kappa)\,D_0.L$; a proof that this base-changed chart is an affine open; and, for every $1$-simplex $s$ of $\mathcal U$ (a strictly monotone pair of indices, with $\mathcal U.\mathrm{inter}\,s$ the intersection of the two corresponding opens), a ring isomorphism $\sigma_s : \kappa \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s) \to \Gamma(\operatorname{pullback} D_0.f\,(\mathrm{specMap}\,B\,\kappa), (\mathcal U.\mathrm{baseChange}\,D_0.f\,\kappa).\mathrm{inter}\,s)$, the $B$-algebra structures on sections being those induced by the structure morphisms, such that $\sigma_s(1 \otimes x)$ is the restriction along the inclusion of the base-changed intersection of the image of $x$ under the first projection's map of sections, and $\sigma_s(a \otimes 1)$ is the structural scalar $a$.
--
--   This packages, in a single existential statement, the geometric frame used for the re-gluing calculus on a bare deformation: a finite affine chart system in which the unit section of the group law lives in a distinguished chart, together with the identification of the Čech data of the residue fibre as the base change of the Čech data upstairs. It is cited in the construction producing, from separability and annihilation hypotheses on a kernel, the factorisations of morphisms used downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_orderedAffineCover_unit_chart_frame_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_orderedAffineCover_unit_chart_frame_bare
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [CommRing B₁] [Algebra B B₁]
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f] :
    ∃ (𝒰 : D₀.A.OrderedAffineCover) (i₀ : 𝒰.ι)
      (e₀ : Spec (CommRingCat.of B) ⟶ ↑(𝒰.U i₀)) (_ : e₀ ≫ (𝒰.U i₀).ι = (D₀.L.one (𝟙 _)).1)
      (e₁ : Spec (CommRingCat.of (ResidueField B)) ⟶ (((𝒰.baseChange D₀.f (ResidueField B)).U i₀) : Scheme.{0}))
      (_ : e₁ ≫ ((𝒰.baseChange D₀.f (ResidueField B)).U i₀).ι = ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).one (𝟙 _)).1)
      (_ : IsAffineOpen ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))
      (σ : ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s)) ≃+* Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s)),
      (∀ (s : 𝒰.Idx 1) (x : Γ(D₀.A, 𝒰.inter s)),
        letI := algebraOfHom D₀.f (𝒰.inter s)
        σ s ((1 : (ResidueField B)) ⊗ₜ[B] x) =
          ((pullback D₀.f (specMap B (ResidueField B))).presheaf.map (homOfLE (𝒰.baseChange_inter_le D₀.f (ResidueField B) s)).op).hom
            (((pullback.fst D₀.f (specMap B (ResidueField B))).app (𝒰.inter s)).hom x)) ∧
      (∀ (s : 𝒰.Idx 1) (a : (ResidueField B)),
        letI := algebraOfHom D₀.f (𝒰.inter s)
        letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).inter s)
        σ s (a ⊗ₜ[B] (1 : Γ(D₀.A, 𝒰.inter s))) = algebraMap (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s) a) := by sorry
