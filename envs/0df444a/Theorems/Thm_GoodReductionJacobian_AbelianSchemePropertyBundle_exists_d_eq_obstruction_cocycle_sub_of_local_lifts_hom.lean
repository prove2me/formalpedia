-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_obstruction_cocycle_sub_of_local_lifts_hom
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_obstruction_cocycle_sub_of_local_lifts_hom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/aef3f3bb-0902-5a5c-b268-6084baf3f610
-- title:
--   Independence of the obstruction cochain of the chosen local lifts
-- statement:
--   Fix a surjection $\pi : T' \to T$ of commutative rings whose kernel is nilpotent and satisfies $\ker\pi\cdot\mathfrak m_{T'}=0$ and $\ker\pi\subseteq\mathfrak m_{T'}$, with $T'$ artinian local and $\operatorname{ResidueField} T'$ algebraically closed, together with $\rho : T \to \operatorname{ResidueField} T'$ factoring the residue map through $\pi$. Over $\operatorname{Spec} T$ are given $f_0 : A_0 \to \operatorname{Spec} T$ and $f_0' : A_0' \to \operatorname{Spec} T$, each carrying a commutative relative group law and satisfying `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, and a relative group law), and a morphism $u_0 : A_0 \to A_0'$ over $\operatorname{Spec} T$; over $\operatorname{Spec} T'$ are given smooth proper $f : A \to \operatorname{Spec} T'$ (separated) and $f' : A' \to \operatorname{Spec} T'$ with pullback squares $g : A_0 \to A$, $g' : A_0' \to A'$ along $\operatorname{Spec}\pi$, and a section $e'$ of $f'$ reducing to the identity section of the group law on $A_0'$. Further data: a finite-dimensional $\operatorname{ResidueField} T'$-module $V$ with compatible $T'$-action and an injective $\iota : V \to T'$ of $T'$-modules whose image is $\ker\pi$; an ordered affine cover $\mathcal W$ of $A$; two families $m, m' : \mathcal W.U i \to A'$ of morphisms over $f$, each reducing on the $T$-fibre to $u_0$ followed by $g'$; the fibre $f_k' : A_k' \to \operatorname{Spec}\operatorname{ResidueField} T'$ of $f_0'$ along $\operatorname{Spec}\rho$ with relative group law $L_k'$, an affine open $U_{e'}\subseteq A_k'$ containing a point $e_1'$ lying over the identity section of $L_k'$; and the fibre $b_k : A_k \to A$ of $f$ along the residue map, an affine morphism, with ring isomorphisms $\sigma_s : \operatorname{ResidueField} T' \otimes_{T'} \Gamma(A, \mathcal W.\mathrm{inter}\,s) \cong \Gamma(A_k, (\mathcal W.\mathrm{comap}\,b_k).\mathrm{inter}\,s)$ compatible with both structure maps. Let $c$ and $c'$ be derivations of $\Gamma(A_k', U_{e'})$ at the evaluation map attached to $e_1'$ (that is, $\operatorname{ResidueField} T'$-linear maps $D$ with $D(ab)=\mathrm{ev}(a)D(b)+\mathrm{ev}(b)D(a)$) with values in the $\operatorname{ResidueField} T'$-linear maps from $V^{\vee}$ to the Čech $1$-cochains of the unit $\mathcal O$-module presheaf of $y_k$ on $\mathcal W.\mathrm{comap}\,b_k$, and assume that for every index $s$ of length one the component of $c$ (respectively $c'$) at $s$ is obtained, via $\sigma_s$, from a system of tangent coordinates in the sense of `IsTangentCoordsOfPairAt` for the pair of morphisms induced by $m$ (respectively $m'$) on the two members of $s$, relative to $\ker\pi$, $V$, $\iota$, the group law $L_k'$ and the chart $U_{e'}$. Then there exists a derivation $b$ of $\Gamma(A_k', U_{e'})$ at the same evaluation map, with values in the maps from $V^{\vee}$ to Čech $0$-cochains, such that for all $a \in \Gamma(A_k', U_{e'})$ and all $\xi \in V^{\vee}$ one has $d^0(b\,a\,\xi) = c\,a\,\xi - c'\,a\,\xi$.
--
--   This is the well-definedness step for the obstruction to lifting a morphism of abelian schemes along a small surjection: the two obstruction $1$-cochains attached to two systems of local lifts of the same $u_0$ differ by a Čech coboundary, so that the obstruction class in the first Čech cohomology group, with coefficients in point derivations at the identity tensored with $V^{\vee}$, depends only on $u_0$ and on the chosen lifts $A$, $A'$. It feeds the criterion that a global lift of $u_0$ exists exactly when the obstruction cochain is a coboundary, and the Hochschild-type cocycle computation for bare deformations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_obstruction_cocycle_sub_of_local_lifts_hom.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct
  AlgebraicGeometry.SmallExtension Scheme.TwoAffineOpenCover

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_obstruction_cocycle_sub_of_local_lifts_hom
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)

    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (hc₀ : L₀.IsCommutative)
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))

    {A₀' : Scheme.{u}} (f₀' : A₀' ⟶ Spec (CommRingCat.of T)) (L₀' : RelativeGroupLaw T f₀') (hc₀' : L₀'.IsCommutative)
    (h₀' : AbelianSchemePropertyBundle T f₀')
    {A' : Scheme.{u}} (f' : A' ⟶ Spec (CommRingCat.of T')) (hs' : Smooth f') (hp' : IsProper f')
    (g' : A₀' ⟶ A') (hg' : IsPullback g' f₀' f' (Spec.map (CommRingCat.ofHom π)))
    (e' : SchemeHomOver (𝟙 (Spec (CommRingCat.of T'))) f')
    (he' : Spec.map (CommRingCat.ofHom π) ≫ e'.1 = (L₀'.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ g')

    (u₀ : A₀ ⟶ A₀') (hu₀ : u₀ ≫ f₀' = f₀)

    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

    [IsSeparated f]
    (𝒲 : A.OrderedAffineCover)
    (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A')
    (hmf : ∀ i, m i ≫ f' = (𝒲.U i).ι ≫ f)
    (hmμ : ∀ i, morphismRestrict g (𝒲.U i) ≫ m i = (g ⁻¹ᵁ (𝒲.U i)).ι ≫ u₀ ≫ g')

    (m' : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A')
    (hmf' : ∀ i, m' i ≫ f' = (𝒲.U i).ι ≫ f)
    (hmμ' : ∀ i, morphismRestrict g (𝒲.U i) ≫ m' i = (g ⁻¹ᵁ (𝒲.U i)).ι ≫ u₀ ≫ g')

    {Ak' : Scheme.{u}} (fk' : Ak' ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk' : RelativeGroupLaw (ResidueField T') fk')
    (i₀' : Ak' ⟶ A₀') (hi₀' : IsPullback i₀' fk' f₀' (Spec.map (CommRingCat.ofHom ρ)))
    (Ue' : Ak'.Opens) (hUe' : IsAffineOpen Ue')
    (e₁' : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue' : Scheme.{u})) (he₁' : e₁' ≫ Ue'.ι = (Lk'.one (𝟙 _)).1)

    {Ak : Scheme.{u}} (bk : Ak ⟶ A) [IsAffineHom bk] (yk : Ak ⟶ Spec (CommRingCat.of (ResidueField T')))
    (hbk : IsPullback bk yk f (Spec.map (CommRingCat.ofHom (residue T'))))
    (σ : ∀ {n : ℕ} (s : 𝒲.Idx n),
      letI := algebraOfHom f (𝒲.inter s)
      ((ResidueField T') ⊗[T'] Γ(A, 𝒲.inter s)) ≃+* Γ(Ak, (𝒲.comap bk).inter s))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒲.Idx n) (x : Γ(A, 𝒲.inter s)),
      letI := algebraOfHom f (𝒲.inter s)
      σ s ((1 : ResidueField T') ⊗ₜ[T'] x) =
        (Ak.presheaf.map (homOfLE (𝒲.comap_inter_le bk s)).op).hom ((bk.app (𝒲.inter s)).hom x))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒲.Idx n) (a : ResidueField T'),
      letI := algebraOfHom f (𝒲.inter s)
      letI := algebraOfHom yk ((𝒲.comap bk).inter s)
      σ s (a ⊗ₜ[T'] (1 : Γ(A, 𝒲.inter s))) = algebraMap (ResidueField T') Γ(Ak, (𝒲.comap bk).inter s) a)

    (c : letI := algebraOfHom fk' Ue'
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak', Ue')
          ((Ue'.topIso.inv ≫ e₁'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit yk).cochain (𝒲.comap bk) 1)))
    (hc : letI := algebraOfHom fk' Ue'
      (∀ s : 𝒲.Idx 1,
        letI := algebraOfHom f (𝒲.inter s)
        ∃ cs : Γ(Ak', Ue') → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(A, 𝒲.inter s))),
          IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, 𝒲.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫
              A.homOfLE (𝒲.inter_le s 0) ≫ m (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫
              A.homOfLE (𝒲.inter_le s 1) ≫ m (s.1 1))
            fk' Lk' (i₀' ≫ g') Ue' cs ∧
          ∀ (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V), σ s (cs a ξ) = c.1 a ξ s))
    (c' : letI := algebraOfHom fk' Ue'
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak', Ue')
          ((Ue'.topIso.inv ≫ e₁'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit yk).cochain (𝒲.comap bk) 1)))
    (hc' : letI := algebraOfHom fk' Ue'
      (∀ s : 𝒲.Idx 1,
        letI := algebraOfHom f (𝒲.inter s)
        ∃ cs : Γ(Ak', Ue') → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(A, 𝒲.inter s))),
          IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, 𝒲.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫
              A.homOfLE (𝒲.inter_le s 0) ≫ m' (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫
              A.homOfLE (𝒲.inter_le s 1) ≫ m' (s.1 1))
            fk' Lk' (i₀' ≫ g') Ue' cs ∧
          ∀ (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V), σ s (cs a ξ) = c'.1 a ξ s)) :
    letI := algebraOfHom fk' Ue'
    ∃ b : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak', Ue')
          ((Ue'.topIso.inv ≫ e₁'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit yk).cochain (𝒲.comap bk) 0)),
      ∀ (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit yk).d (𝒲.comap bk) 0 (b.1 a ξ) = c.1 a ξ - c'.1 a ξ := by sorry
