-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_lift_of_pointDerivations_coboundary_of_smooth_source
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_lift_of_pointDerivations_coboundary_of_smooth_source
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/67d2b18f-f74f-5c19-8822-92e36d0e04b2
-- title:
--   Lifting a morphism when the obstruction cochain is a coboundary
-- statement:
--   Let $T'$ be an artinian local ring with algebraically closed residue field $k=\mathrm{ResidueField}\,T'$, let $T$ be a commutative ring and $\pi:T'\to T$ a surjective homomorphism whose kernel is nilpotent, contained in the maximal ideal, and satisfies $(\ker\pi)\cdot\mathfrak m_{T'}=0$. Let $f_0:A_0\to\operatorname{Spec}T$ and $f:A\to\operatorname{Spec}T'$ with $f$ smooth and separated, and $g:A_0\to A$ exhibiting $A_0$ as the base change of $A$ along $\operatorname{Spec}\pi$. Let $f_0':A_0'\to\operatorname{Spec}T$ carry a commutative relative group law $L_0'$ and satisfy `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, a relative group law exists), let $f':A'\to\operatorname{Spec}T'$ be smooth and proper with $g':A_0'\to A'$ exhibiting $A_0'$ as its base change along $\operatorname{Spec}\pi$, and let $e'$ be a section of $f'$ over $\operatorname{Spec}T'$ whose composite with $\operatorname{Spec}\pi$ is the unit section of $L_0'$ followed by $g'$. Let $u_0:A_0\to A_0'$ be a morphism over $T$. Fix $\rho:T\to k$ with $\rho\circ\pi$ the residue map, a finite $k$-vector space $V$ with compatible $T'$-structure, and an injective $T'$-linear $\iota:V\to T'$ whose image is $\ker\pi$. Fix an ordered affine cover $\mathcal W$ of $A$ (a finite linearly ordered family of affine opens covering $A$) together with morphisms $m_i:\mathcal W.U_i\to A'$ over $f$ which restrict along $g$ to $u_0$ followed by $g'$, i.e. $g|_{\mathcal W.U_i}$ followed by $m_i$ equals the inclusion of $g^{-1}(\mathcal W.U_i)$ followed by $u_0\ggg'$. Fix moreover: $f_k':A_k'\to\operatorname{Spec}k$ with a relative group law $L_k'$ and $i_0':A_k'\to A_0'$ exhibiting $A_k'$ as the base change of $f_0'$ along $\operatorname{Spec}\rho$; an affine open $U_{e'}\subseteq A_k'$ with a point $e_1':\operatorname{Spec}k\to U_{e'}$ lying over the unit of $L_k'$; $b_k:A_k\to A$ affine with $y_k:A_k\to\operatorname{Spec}k$ exhibiting $A_k$ as the special fibre of $f$; and isomorphisms $\sigma_s:k\otimes_{T'}\Gamma(A,\mathcal W.\mathrm{inter}\,s)\cong\Gamma(A_k,(\mathcal W.\mathrm{comap}\,b_k).\mathrm{inter}\,s)$, for all simplices $s$ of $\mathcal W$, compatible with the base-change map on sections and with the $k$-algebra structures. Finally let $c$ be a $k$-linear map on $\Gamma(A_k',U_{e'})$ satisfying the Leibniz rule at the point determined by $e_1'$, with values in $\operatorname{Hom}_k(V^\ast,\,1\text{-cochains of the unit }\mathcal O\text{-module presheaf of }y_k\text{ on }\mathcal W.\mathrm{comap}\,b_k)$, such that for every $1$-simplex $s=(i<j)$ there are functions $c_s$ on $\Gamma(A_k',U_{e'})$ with values in $\operatorname{Hom}_k(V^\ast,k\otimes_{T'}\Gamma(A,\mathcal W.\mathrm{inter}\,s))$ which are tangent coordinates, in the sense of `IsTangentCoordsOfPairAt` for $\ker\pi$, $V$, $\iota$ and $C=\Gamma(A,\mathcal W.\mathrm{inter}\,s)$ (existence of a map $w_0$ from the spectrum of the thickening into $A_k'$ over the base with $w_0$ followed by $i_0'\ggg'$ a tangent vector of the pair in the sense of `IsTangentOfPair`, a lift $w_1$ into $U_{e'}$ of the $L_k'$-translate of $w_0$ to the unit, and $c_s$ the tangent coordinates of the resulting chart homomorphism), for the pair of morphisms $\operatorname{Spec}\Gamma(A,\mathcal W.\mathrm{inter}\,s)\to A'$ obtained from $m_i$ and $m_j$ by restricting to the intersection, and such that $\sigma_s\circ c_s$ agrees with the $s$-component of $c$. Let $b$ be a similar Leibniz map with values in $\operatorname{Hom}_k(V^\ast,0\text{-cochains})$ with $\mathrm{d}\,b=c$ pointwise. Then there is a morphism $u:A\to A'$ with $u\gg f'=f$ and $g\gg u=u_0\ggg'$.
--
--   This is the gluing step of the deformation-theoretic lifting argument for morphisms along a small surjection $T'\to T$: once the local lifts $m_i$ of $u_0$ are available and their discrepancy $1$-cochain $c$, measured in tangent coordinates at the unit section, is a coboundary $\mathrm{d}b$, the corrected local lifts agree on overlaps and glue to a global lift $u$ over $T'$. It is used in the construction of lifts of charts for bare deformations, via [`GoodReductionJacobian.BareDeformation.exists_chart_lift_comp_eq_of_isRegluingBy_bare`](thm.html#GoodReductionJacobian.BareDeformation.exists_chart_lift_comp_eq_of_isRegluingBy_bare).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_lift_of_pointDerivations_coboundary_of_smooth_source.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_lift_of_pointDerivations_coboundary_of_smooth_source
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)

    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T))
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f)
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
    (b : letI := algebraOfHom fk' Ue'
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak', Ue')
          ((Ue'.topIso.inv ≫ e₁'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit yk).cochain (𝒲.comap bk) 0)))
    (hb : letI := algebraOfHom fk' Ue'
      ∀ (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit yk).d (𝒲.comap bk) 0 (b.1 a ξ) = c.1 a ξ) :
    ∃ u : A ⟶ A', u ≫ f' = f ∧ g ≫ u = u₀ ≫ g' := by sorry
