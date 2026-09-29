-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_isTangentCoordsOfPairAt_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_isRegluingBy_isTangentCoordsOfPairAt_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/ae4e5c9f-e2e1-5e53-b073-6210fdd679dd
-- title:
--   Regluing a bare deformation along a Čech tangent cocycle
-- statement:
--   Let $B$ be an Artinian local ring with algebraically closed residue field $k = \mathrm{ResidueField}\,B$ and let $B \to B_1$ be a surjective $B$-algebra with nilpotent kernel $J$ satisfying $J \subseteq \mathfrak m_B$ and $J\,\mathfrak m_B = 0$; let $V$ be a finite-dimensional $k$-space, also a $B$-module compatibly, with an injective $B$-linear $\iota : V \to B$ whose range is $J$. Let $f_1 : A_1 \to \operatorname{Spec} B_1$ carry a commutative relative group law $L_1$ and satisfy `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, group law), and let $D_0$ be a bare deformation of $(f_1,L_1)$ to $B$ — a scheme $D_0.A$ with $D_0.f$ to $\operatorname{Spec} B$, a commutative relative group law $D_0.L$, the bundle of properties, and a map $D_0.g$ making $f_1$ the base change of $D_0.f$ along $B \to B_1$ compatibly with the multiplications — with $D_0.f$ separated. Let $\mathcal U$ be a finite ordered affine open cover of $D_0.A$ (linearly ordered index set, affine opens covering the whole space), $i_0$ an index, $e_0 : \operatorname{Spec} B \to \mathcal U.U\,i_0$ a factorisation of the unit section of $D_0.L$, and $e_1 : \operatorname{Spec} k \to (\mathcal U.\mathrm{baseChange}\,D_0.f\,k).U\,i_0$ a factorisation of the unit section of the base-changed group law on the special fibre $A_k = D_0.A \times_{\operatorname{Spec} B} \operatorname{Spec} k$. For each one-index pair $s$ (a strictly monotone pair in $\mathcal U.\iota$, with overlap $\mathcal U.\mathrm{inter}\,s$) let $\sigma_s$ be a ring isomorphism $k \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s) \cong \Gamma(A_k, (\mathcal U.\mathrm{baseChange})\,\mathrm{inter}\,s)$, assumed to send $1 \otimes x$ to the restriction of the pullback of $x$ along the first projection and $a \otimes 1$ to the image of $a$ under the structure map. Finally let $c$ be a $k$-linear point derivation of $\Gamma(A_k, (\mathcal U.\mathrm{baseChange})\,U\,i_0)$ at the evaluation $e_1$ (Leibniz rule with respect to that evaluation) with values in $\operatorname{Hom}_k(V^\vee, \check C^1(\mathcal U_k, \mathcal O))$, where the Čech cochains are those of the unit $\mathcal O$-module presheaf for the special-fibre structure map, and assume each value $c(a)(\xi)$ is killed by the Čech differential $d^1$. The conclusion is that there exist self-isomorphisms $\tau_s$ of every overlap $\mathcal U.\mathrm{inter}\,s$ and a bare deformation $D$ of $(f_1,L_1)$ to $B$ such that $D_0.\mathrm{IsRegluingBy}\,\mathcal U\,\tau\,D$ holds — the $\tau_s$ lie over $\operatorname{Spec} B$ and fix the restrictions of $D_0.g$, and there are open immersions of the $\mathcal U.U\,i$ into $D.A$ over $D_0.f$, jointly surjective, compatible with $D_0.g$, and glued on overlaps through the $\tau_s$ — and such that for every $s$ there is a function $c_s$ from $\Gamma(A_k, (\mathcal U.\mathrm{baseChange})\,U\,i_0)$ to $\operatorname{Hom}_k(V^\vee, k \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s))$ satisfying `IsTangentCoordsOfPairAt` for the ideal $J$, the data $(V,\iota)$, the ring $C = \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s)$, the pair of maps given by the canonical $\operatorname{Spec} C \to D_0.A$ and by the composite of the inverse of the affine isomorphism with $\tau_s$ followed by the inclusion of the overlap, the special-fibre structure map with its base-changed group law, and the chart $U\,i_0$ of the base-changed cover — that is, there are a map $w_0$ from the spectrum of the thickening $(k \otimes_B C) \otimes_k (k \oplus V)$ to $A_k$ over the canonical base and a lift $w_1$ into that chart, such that the composite of $w_0$ with the map to $D_0.A$ is a tangent vector of the pair in the sense of `IsTangentOfPair` (coming from a Schlessinger map on the pair ring of $J$ and $C$), $w_1$ is the translate of $w_0$ by the inverse of the unit, and $c_s$ is the tangent-coordinate function of the resulting chart homomorphism; moreover $\sigma_s(c_s(a)(\xi))$ equals the $s$-component of $c(a)(\xi)$ for all $a$ and $\xi$.
--
--   This is the construction step showing that a Čech $1$-cocycle of $V$-valued tangent fields on the special fibre acts on bare deformations of an abelian scheme across a small extension $B \to B_1$: the cocycle is used to reglue the given deformation $D_0$ along the overlaps of an affine cover, producing a new deformation whose overlap tangent coordinates realise the prescribed cocycle. It feeds the classification of bare deformations over dual numbers for fake elliptic curves and the comparison of deformations through separability elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_isTangentCoordsOfPairAt_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_isRegluingBy_isTangentCoordsOfPairAt_bare
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
    :
    ∃ (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s))) (D : BareDeformation f₁ L₁ B),
      D₀.IsRegluingBy 𝒰 τ D ∧
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
            σ s (cs a ξ) = (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ s := by sorry
