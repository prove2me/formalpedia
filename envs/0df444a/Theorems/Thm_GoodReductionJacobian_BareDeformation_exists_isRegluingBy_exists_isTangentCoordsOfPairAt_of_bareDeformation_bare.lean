-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_exists_isTangentCoordsOfPairAt_of_bareDeformation_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_isRegluingBy_exists_isTangentCoordsOfPairAt_of_bareDeformation_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/7ba6d116-189e-5df7-acb7-3e64f7a553ed
-- title:
--   Bare deformations are regluings carrying a cocycle tangent class
-- statement:
--   Let $B$ be an Artinian local ring with algebraically closed residue field $\kappa =$ `ResidueField B`, let $B_1$ be a $B$-algebra whose structure map is surjective with nilpotent kernel $I$, and assume the smallness conditions $I\cdot\mathfrak m_B = 0$ and $I \subseteq \mathfrak m_B$; let $V$ be a finite-dimensional $\kappa$-vector space, carrying compatible $B$- and $\kappa^{\mathrm{op}}$-actions, together with an injective $B$-linear $\iota : V \to B$ whose image is exactly $I$. Let $f_1 : A_1 \to \operatorname{Spec} B_1$ carry a commutative relative group law $L_1$ and satisfy the abelian-scheme bundle (smooth, proper, connected fibres, a relative group law exists). Let $D_0$ be a bare deformation of $(f_1,L_1)$ to $B$ — a scheme with a structure map to $\operatorname{Spec} B$, a commutative relative group law, the abelian-scheme bundle, and a map from $A_1$ making a pullback square over $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ compatibly with the group laws — with separated structure map, and let $\mathcal U$ be a finite ordered affine cover of $D_0.A$. Fix an index $i_0$, a section $e_0 : \operatorname{Spec} B \to U_{i_0}$ inducing the unit of $D_0.L$, the corresponding unit $e_1$ of the chart of the $\kappa$-base change, and ring isomorphisms $\sigma_s : \kappa \otimes_B \Gamma(D_0.A, \mathcal U_s) \cong \Gamma(\cdot, (\mathcal U_\kappa)_s)$ on each $1$-simplex overlap, pinned on $1 \otimes x$ and on $a \otimes 1$ by the two compatibility hypotheses. Then for any second bare deformation $D$ of $(f_1,L_1)$ to $B$ there exist self-isomorphisms $\tau_s$ of the overlaps $\mathcal U_s$, $s$ a $1$-simplex, and a $\kappa$-point derivation $c$ of $\Gamma(\cdot, (\mathcal U_\kappa)_{i_0})$ at the evaluation homomorphism of $e_1$, with values in $\operatorname{Hom}_\kappa(V^\vee, \check C^1(\mathcal U_\kappa, \mathcal O))$, such that: every value $c(a)(\xi)$ is killed by the Čech differential $d^1$; $D_0$.`IsRegluingBy` $\mathcal U$ $\tau$ $D$ holds, i.e. each $\tau_s$ is a morphism over $\operatorname{Spec} B$ fixing the restriction of $D_0.g$, and there are jointly surjective open immersions $U_i \to D.A$ over $\operatorname{Spec} B$ compatible with $D_0.g$ and $D.g$ and glued through the $\tau_s$; and for each $s$ there is a map $c_s$ on $\Gamma(\cdot, (\mathcal U_\kappa)_{i_0})$ with values in $\operatorname{Hom}_\kappa(V^\vee, \kappa \otimes_B \Gamma(D_0.A, \mathcal U_s))$ which is a tangent-coordinate system, in the sense of `IsTangentCoordsOfPairAt` for the ideal $I$, $V$, $\iota$, for the pair consisting of the canonical map from $\operatorname{Spec}$ of the overlap ring and of that map composed with $\tau_s$ followed by the inclusion of $\mathcal U_s$, relative to the $\kappa$-fibre of $D_0$ with its base-changed group law and the chart $(\mathcal U_\kappa)_{i_0}$, and such that $\sigma_s(c_s(a)(\xi))$ is the $s$-component of $c(a)(\xi)$ for all $a$ and $\xi$.
--
--   This is the local-triviality-plus-cocycle step in the deformation theory of abelian schemes along a small surjection: any two bare deformations of the same abelian scheme over $B_1$ differ by a regluing of a fixed affine cover, and the resulting discrepancy is recorded by a Čech $1$-cocycle with values in the tangent sheaf twisted by $V \cong I$. It is used in the classification of bare deformations over dual numbers for fake elliptic curves over an algebraically closed field of positive characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_exists_isTangentCoordsOfPairAt_of_bareDeformation_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_isRegluingBy_exists_isTangentCoordsOfPairAt_of_bareDeformation_bare
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

    (D : BareDeformation f₁ L₁ B) :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
    ∃ (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
      (c : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)))),
      (∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1 (c.1 a ξ) = 0) ∧
      D₀.IsRegluingBy 𝒰 τ D ∧
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = c.1 a ξ s := by sorry
