-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_local_lifts_twisted_hom_obstruction_cochain_of_isRegluingBy_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_local_lifts_twisted_hom_obstruction_cochain_of_isRegluingBy_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/2706faab-c224-5af3-8ce9-4ddc6ad2608b
-- title:
--   Chartwise lifts and their τ-twisted obstruction cochain
-- statement:
--   Let $B$ be an Artinian local ring with algebraically closed residue field $\kappa$, and let $B_1$ be a $B$-algebra whose structure map is surjective with nilpotent kernel $J$ satisfying $J\subseteq\mathfrak m_B$ and $J\cdot\mathfrak m_B=0$; let $f_1:A_1\to\operatorname{Spec}B_1$ carry a commutative relative group law $L_1$ and the property bundle `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, a group law exists). Let $V$ be a finite-dimensional $\kappa$-vector space which is also a $B$-module compatibly with the residue map, and $\iota:V\to B$ an injective $B$-linear map whose range is $J$. Let $D_0$ be a bare deformation of $(f_1,L_1)$ over $B$, that is, a scheme $D_0.A$ with a commutative relative group law $D_0.L$ over $B$, the same property bundle, and $D_0.g:A_1\to D_0.A$ making $f_1$ the base change of $D_0.f$ along $B\to B_1$ and compatible with the group laws, with $D_0.f$ separated. Fix a finite ordered affine open cover $\mathcal U$ of $D_0.A$, an index $i_0$, a section $e_0$ of $\mathcal U.U\,i_0$ over $\operatorname{Spec}B$ lifting the identity section of $D_0.L$, the analogous section $e_1$ of the chart $U_{i_0,\kappa}$ of the base-changed cover $\mathcal U_\kappa$ on $X_\kappa=D_0.A\times_{\operatorname{Spec}B}\operatorname{Spec}\kappa$ lifting the identity of the base-changed group law, and, for each pair $s$ of indices, ring isomorphisms $\sigma_s:\kappa\otimes_B\Gamma(D_0.A,U_s)\cong\Gamma(X_\kappa,U_{s,\kappa})$ compatible with $1\otimes x$ (sent to the restriction of the pullback of $x$) and with $a\otimes 1$ (sent to the image of $a$ under the structure map). Let $\tau_s$ be self-isomorphisms of the overlaps $U_s$, let $D$ be a bare deformation with $D_0.\mathrm{IsRegluingBy}\ \mathcal U\ \tau\ D$ (the $\tau_s$ commute with $D_0.f$ and with the restrictions of $D_0.g$, and there are jointly surjective open immersions $U_i\to D.A$ over $D_0.f$ compatible with $D_0.g$ and glued on overlaps through the $\tau_s$), assume $U_{i_0,\kappa}$ affine, and let $\varphi_1:A_1\to A_1$ be a morphism over $\operatorname{Spec}B_1$ and $j_\kappa:X_\kappa\to A_1$ a morphism with $j_\kappa$ followed by $D_0.g$ equal to the first projection. Then there exist morphisms $m_i:U_i\to D.A$ over $B$ (i.e. $m_i$ followed by $D.f$ is the inclusion followed by $D_0.f$) such that the restriction of $D_0.g$ over $U_i$ followed by $m_i$ equals the inclusion of $D_0.g^{-1}U_i$ followed by $\varphi_1$ and then $D.g$, together with a point derivation $c'$ of $\Gamma(X_\kappa,U_{i_0,\kappa})$ at the evaluation homomorphism determined by $e_1$, with values in the $\kappa$-linear maps from the dual of $V$ to the $1$-cochains of the structure-sheaf $\mathcal O$-module presheaf on $\mathcal U_\kappa$, such that for every pair $s$ there is a map $c_s:\Gamma(D_0.A,U_s)\to\operatorname{Hom}_\kappa(V^\vee,\kappa\otimes_B\Gamma(D_0.A,U_s))$ which is a system of tangent coordinates, in the sense of `IsTangentCoordsOfPairAt` for the ideal $J$, $V$, $\iota$ and $C=\Gamma(D_0.A,U_s)$, of the $\tau$-twisted pair of $C$-points of $D.A$ given by the inverse of the canonical isomorphism $U_s\cong\operatorname{Spec}C$ followed, respectively, by the inclusion into $U_{s_0}$ and $m_{s_0}$, and by $\tau_s$, the inclusion into $U_{s_1}$ and $m_{s_1}$, taken relative to the projection $X_\kappa\to\operatorname{Spec}\kappa$, the base-changed group law, the morphism $j_\kappa$ followed by $D.g$, and the chart $U_{i_0,\kappa}$; and $\sigma_s(c_s(a)(\xi))=c'(a)(\xi)_s$ for all $a$ and all $\xi\in V^\vee$. Unfolded, the tangent-coordinates condition asserts the existence of a point $w_0$ of $X_\kappa$ with values in the thickening $(\kappa\otimes_BC)\otimes_\kappa(\kappa\oplus V)$ lying over the tangent base, such that $w_0$ followed by $j_\kappa\ggg D.g$ exhibits the given pair as a tangent of a pair in the sense of `IsTangentOfPair`, a lift $w_1$ into the chart of the translate of $w_0$ to the identity section by the group law, and $c_s$ equal to the tangent coordinates of the induced ring homomorphism on $\Gamma(X_\kappa,U_{i_0,\kappa})$.
--
--   This is the existence half of the obstruction calculus for extending an endomorphism of the closed fibre across a re-glued deformation: on each affine chart the morphism $\varphi_1$ followed by $D.g$ lifts across the nilpotent thickening $D_0.g^{-1}U_i\to U_i$ because $D.A\to\operatorname{Spec}B$ is smooth, and the discrepancies of the chosen lifts on the $\tau$-twisted overlaps are recorded as a single point derivation with values in $\operatorname{Hom}_\kappa(V^\vee,\check C^1(\mathcal U_\kappa,\mathcal O))$. It supplies the data block consumed by [`GoodReductionJacobian.BareDeformation.exists_comp_eq_comp_iff_add_map_tmul_sub_eq_zero_of_isRegluingBy_of_local_lifts_bare`](thm.html#GoodReductionJacobian.BareDeformation.exists_comp_eq_comp_iff_add_map_tmul_sub_eq_zero_of_isRegluingBy_of_local_lifts_bare), which converts the vanishing of that cochain into the existence of a global endomorphism of the re-glued deformation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_local_lifts_twisted_hom_obstruction_cochain_of_isRegluingBy_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_local_lifts_twisted_hom_obstruction_cochain_of_isRegluingBy_bare
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
    (D : BareDeformation f₁ L₁ B) (hD : D₀.IsRegluingBy 𝒰 τ D)
    (hU : IsAffineOpen ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))

    (φ₁ : A₁ ⟶ A₁) (hφ₁ : φ₁ ≫ f₁ = f₁)
    (jκ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ A₁) (hjκ : jκ ≫ D₀.g = (pullback.fst D₀.f (specMap B (ResidueField B)))) :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
    ∃ (mp : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A)
      (_ : ∀ i, mp i ≫ D.f = (𝒰.U i).ι ≫ D₀.f)
      (_ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ mp i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D.g)
      (c' : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)))),
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 0) ≫ mp (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ mp (s.1 1))
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = c'.1 a ξ s := by sorry
