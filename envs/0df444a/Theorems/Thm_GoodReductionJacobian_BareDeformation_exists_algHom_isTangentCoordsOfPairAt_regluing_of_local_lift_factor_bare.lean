-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_algHom_isTangentCoordsOfPairAt_regluing_of_local_lift_factor_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_algHom_isTangentCoordsOfPairAt_regluing_of_local_lift_factor_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/cd77b61f-36ae-5245-a7aa-24b8d0bb694a
-- title:
--   Transporting pair tangent coordinates to a subchart of a local lift
-- statement:
--   Let $B$ be a local Artinian commutative ring, $B_1$ a commutative $B$-algebra, and write $I=\ker(B\to B_1)$; assume $I\cdot\mathfrak m_B=0$ and $I\subseteq\mathfrak m_B$. Let $f_1:A_1\to\operatorname{Spec}B_1$ carry a relative group law $L_1$. Let $V$ be a finite-dimensional module over $\kappa=\mathrm{ResidueField}\,B$, also a $B$-module compatibly with the tower $B\to\kappa$ and with matching left and right $\kappa$-actions, and let $\iota:V\to B$ be an injective $B$-linear map whose image is $I$. Let $D_0$ and $D$ be bare deformations of $(f_1,L_1)$ over $B$, so each consists of a scheme with a structure morphism to $\operatorname{Spec}B$, a commutative relative group law, the smooth–proper–connected-fibres bundle, and a morphism from $A_1$ exhibiting $A_1$ as the base change along $B\to B_1$ compatibly with the group laws; assume $D_0.f$ separated. Let $\mathcal U$ be an ordered affine cover of $D_0.A$ (a finite linearly ordered family of affine opens with supremum $\top$), $i_0$ an index, and $j_\kappa$ a morphism from the special fibre $\operatorname{pullback}(D_0.f,\operatorname{Spec}\kappa\to\operatorname{Spec}B)$ to $A_1$ with $j_\kappa\circ$ (followed by) $D_0.g$ equal to the first projection. Let $\tau_s$ be self-isomorphisms of the overlaps $\mathcal U.\mathrm{inter}\,s=\bigwedge_j U_{s(j)}$ for $1$-simplices $s$ (strictly increasing pairs); let $\iota D_i:U_i\to D.A$ satisfy the compatibility with $D_0.g$ and $D.g$ over $U_i$ and the gluing law: on each overlap for $s$, the inclusion followed by $\iota D_{s(0)}$ equals $\tau_s$ followed by the inclusion and $\iota D_{s(1)}$. Let $m_i:U_i\to D_0.A$ be morphisms over $\operatorname{Spec}B$. Fix a $1$-simplex $t$, an index $j$, an affine open $W\le U_j$, and $P:W\to\mathcal U.\mathrm{inter}\,t$ whose composite with the inclusion is the inclusion $W\le U_j$ followed by $m_j$. Finally let $cs$ assign to each section over the base-changed chart $(\mathcal U.\mathrm{baseChange})U_{i_0}$ of the special fibre a $\kappa$-linear map $V^\ast\to\kappa\otimes_B\Gamma(D_0.A,\mathcal U.\mathrm{inter}\,t)$, and assume $cs$ satisfies `IsTangentCoordsOfPairAt` for $I$, $V$, $\iota$, $C=\Gamma(D_0.A,\mathcal U.\mathrm{inter}\,t)$, for the pair consisting of the canonical $\mathrm{fromSpec}$ of the overlap and of $\mathrm{isoSpec}^{-1}$ followed by $\tau_t$ and the inclusion, with structure morphism the second projection of the special fibre, group law the base change of $D_0.L$ to $\kappa$, reference morphism the first projection, and chart $(\mathcal U.\mathrm{baseChange})U_{i_0}$; that is, there are a morphism $w_0$ from the spectrum of the thickening $(\kappa\otimes_B C)\otimes_\kappa(\kappa\oplus V)$ to the special fibre over the square-zero base and a lift $w_1$ into the chart of the group-law translate of $w_0$, such that the composite of $w_0$ with the reference morphism is a tangent point of the given pair and $cs$ is the tangent-coordinate function of the induced ring homomorphism on sections. The conclusion: with the $B$-algebra structures on $\Gamma(D_0.A,\mathcal U.\mathrm{inter}\,t)$ and $\Gamma(D_0.A,W)$ coming from $D_0.f$, there exists a $B$-algebra homomorphism $\theta:\Gamma(D_0.A,\mathcal U.\mathrm{inter}\,t)\to\Gamma(D_0.A,W)$ such that $\operatorname{Spec}\theta$ followed by $\mathrm{isoSpec}^{-1}$ of the overlap equals $\mathrm{isoSpec}^{-1}$ of $W$ followed by $P$, and such that $\kappa\otimes\theta$ applied after $cs$ satisfies `IsTangentCoordsOfPairAt` for $I$, $V$, $\iota$, $\Gamma(D_0.A,W)$, for the pair $\bigl(\mathrm{isoSpec}_W^{-1}\,P\,(\text{inclusion})\,\iota D_{t(1)},\ \mathrm{isoSpec}_W^{-1}\,P\,(\text{inclusion})\,\iota D_{t(0)}\bigr)$, with the same second projection and base-changed group law, reference morphism $j_\kappa$ followed by $D.g$, and chart $(\mathcal U.\mathrm{baseChange})U_{i_0}$.
--
--   This is the transport step in the computation of the obstruction to regluing a bare deformation: tangent coordinates of the pair of overlap charts, computed on the overlap $\mathcal U.\mathrm{inter}\,t$, are carried by a $B$-algebra map of section rings onto an affine open $W$ on which a local lift $m_j$ factors through the overlap, and there they become coordinates for the pair of regluing immersions $\iota D_{t(1)},\iota D_{t(0)}$ read in $D.A$. It is used by the two statements expressing the regluing obstruction cocycle as a difference of base-changed terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_algHom_isTangentCoordsOfPairAt_regluing_of_local_lift_factor_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_algHom_isTangentCoordsOfPairAt_regluing_of_local_lift_factor_bare
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    [CommRing B₁] [Algebra B B₁]
    (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥)
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    [Module (ResidueField B)ᵐᵒᵖ V] [IsCentralScalar (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))
    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f] (𝒰 : D₀.A.OrderedAffineCover) (i₀ : 𝒰.ι)

    (jκ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ A₁) (hjκ : jκ ≫ D₀.g = (pullback.fst D₀.f (specMap B (ResidueField B))))

    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation f₁ L₁ B)
    (ιD : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A)
    (hιg : ∀ i, (D₀.g ∣_ 𝒰.U i) ≫ ιD i = (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ D.g)
    (hιglue : ∀ s : 𝒰.Idx 1,
      D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ιD (s.1 0) = (τ s).hom ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ιD (s.1 1))

    (m : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmf : ∀ i, m i ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f)

    (t : 𝒰.Idx 1) (j : 𝒰.ι) (Wo : D₀.A.Opens) (hWo : IsAffineOpen Wo) (hWj : Wo ≤ 𝒰.U j)
    (P : (↑Wo : Scheme.{0}) ⟶ ↑(𝒰.inter t)) (hP : P ≫ (𝒰.inter t).ι = D₀.A.homOfLE hWj ≫ m j)
    (cs : letI := algebraOfHom D₀.f (𝒰.inter t)
      Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter t))))
    (hcs : letI := algebraOfHom D₀.f (𝒰.inter t)
      AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter t)
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 t).fromSpec)
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 t).isoSpec.inv ≫ (τ t).hom ≫ (𝒰.inter t).ι)
        (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs) :
    letI := algebraOfHom D₀.f (𝒰.inter t)
    letI := algebraOfHom D₀.f Wo
    ∃ θ : Γ(D₀.A, 𝒰.inter t) →ₐ[B] Γ(D₀.A, Wo),
      Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 t).isoSpec.inv = hWo.isoSpec.inv ≫ P ∧
      AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, Wo)
        (hWo.isoSpec.inv ≫ P ≫ D₀.A.homOfLE (𝒰.inter_le t 1) ≫ ιD (t.1 1))
        (hWo.isoSpec.inv ≫ P ≫ D₀.A.homOfLE (𝒰.inter_le t 0) ≫ ιD (t.1 0))
        (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
        (fun a => (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) θ).toLinearMap ∘ₗ cs a) := by sorry
