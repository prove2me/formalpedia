-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_pointDerivations_obstruction_cocycle_of_local_lifts_hom_of_smooth_source
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_pointDerivations_obstruction_cocycle_of_local_lifts_hom_of_smooth_source
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/a9aa0d43-3ba2-5420-861a-1bfc49568121
-- title:
--   Obstruction cocycle comparing local lifts along a small extension
-- statement:
--   Let $T'$ be an Artinian local ring with algebraically closed residue field $k=\mathrm{ResidueField}\,T'$, let $\pi:T'\to T$ be a surjective ring map whose kernel $I=\ker\pi$ is nilpotent, contained in the maximal ideal, and satisfies $I\cdot\mathfrak m_{T'}=0$; let $\rho:T\to k$ satisfy $\rho\circ\pi=\mathrm{residue}$. Let $V$ be a finite-dimensional $k$-vector space with a compatible $T'$-module structure and $\iota:V\to T'$ an injective $T'$-linear map with image $I$. Data over the bases: $f:A\to\operatorname{Spec}T'$ smooth and separated with $g:A_0\to A$ exhibiting $f_0:A_0\to\operatorname{Spec}T$ as its base change along $\pi$; $f_0':A_0'\to\operatorname{Spec}T$ carrying a commutative relative group law $L_0'$ and satisfying `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, a relative group law exists); $f':A'\to\operatorname{Spec}T'$ smooth and proper with $g':A_0'\to A'$ its base change along $\pi$, and a section $e'$ of $f'$ reducing to the unit of $L_0'$ followed by $g'$; a morphism $u_0:A_0\to A_0'$ over $T$. Further, an ordered affine cover $\mathcal W$ of $A$ (finitely many affine opens indexed by a linear order, covering $A$) together with morphisms $m_i:\mathcal W.U_i\to A'$ over $T'$ whose reductions modulo $I$ agree with $u_0$ followed by $g'$; the fibre $i_0':A_k'\to A_0'$ of $A_0'$ over $k$ along $\rho$ with a relative group law $L_k'$, an affine open $U_{e'}\subseteq A_k'$ and $e_1':\operatorname{Spec}k\to U_{e'}$ whose composite with the inclusion is the unit of $L_k'$; the special fibre $b_k:A_k\to A$ of $f$ along $T'\to k$, with $b_k$ affine, and ring isomorphisms $\sigma_s:k\otimes_{T'}\Gamma(A,\mathcal W.\mathrm{inter}\,s)\cong\Gamma(A_k,(\mathcal W.\mathrm{comap}\,b_k).\mathrm{inter}\,s)$, for all strictly increasing index tuples $s$, compatible with $1\otimes x\mapsto$ restriction of $b_k^\ast x$ and with the structure maps on $a\otimes 1$. The conclusion asserts the existence of a $k$-linear map $c$ on $\Gamma(A_k',U_{e'})$, with values in $\mathrm{Hom}_k(V^\vee,\check C^1(\mathcal W.\mathrm{comap}\,b_k,\mathcal O))$, satisfying the Leibniz rule with respect to the evaluation $\Gamma(A_k',U_{e'})\to k$ attached to $e_1'$, i.e. a point derivation at the unit, such that: (i) for every pair $s$ of indices there is a family $c_s$ of $V^\vee$-valued tangent coordinates in $k\otimes_{T'}\Gamma(A,\mathcal W.\mathrm{inter}\,s)$ satisfying `IsTangentCoordsOfPairAt` for the ideal $I$, the module $V$ with $\iota$, the ring $\Gamma(A,\mathcal W.\mathrm{inter}\,s)$, and the two morphisms $\operatorname{Spec}\Gamma(A,\mathcal W.\mathrm{inter}\,s)\to A'$ obtained from the inverse of the canonical isomorphism with the intersection, followed by the inclusions into $\mathcal W.U_{s_0}$, $\mathcal W.U_{s_1}$ and then $m_{s_0}$, $m_{s_1}$ — that is, there are a point $w_0$ of $A_k'$ over the thickening $(k\otimes_{T'}C)\otimes_k(k\oplus V)$ whose composite with $i_0'\circ g'$ is a tangent of the pair $(u,v)$ in the sense of `IsTangentOfPair`, and a lift $w_1$ into $U_{e'}$ of the $L_k'$-translate of $w_0$ to the unit, with $c_s$ the tangent coordinates of the resulting chart ring map — and $\sigma_s(c_s(a)(\xi))=c(a)(\xi)(s)$ for all sections $a$ and all $\xi\in V^\vee$; and (ii) every cochain $c(a)(\xi)$ is annihilated by the Čech differential of the presheaf `OModulePresheaf.unit` of $y_k$.
--
--   This is the construction of the Čech obstruction cocycle measuring the failure of the chartwise lifts $m_i$ of $u_0$ to glue: on each overlap the two lifts differ by a point derivation at the unit of the special fibre with values in $I\otimes$ (structure sheaf), and these differences form a $1$-cocycle. It is used in the deformation-theoretic step that lifts a homomorphism of abelian schemes along a small extension, being cited by [`GoodReductionJacobian.BareDeformation.exists_chart_lift_comp_eq_of_isRegluingBy_bare`](thm.html#GoodReductionJacobian.BareDeformation.exists_chart_lift_comp_eq_of_isRegluingBy_bare).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_pointDerivations_obstruction_cocycle_of_local_lifts_hom_of_smooth_source.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_pointDerivations_obstruction_cocycle_of_local_lifts_hom_of_smooth_source
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
      σ s (a ⊗ₜ[T'] (1 : Γ(A, 𝒲.inter s))) = algebraMap (ResidueField T') Γ(Ak, (𝒲.comap bk).inter s) a) :
    letI := algebraOfHom fk' Ue'
    ∃ c : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak', Ue')
          ((Ue'.topIso.inv ≫ e₁'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit yk).cochain (𝒲.comap bk) 1)),

      (∀ s : 𝒲.Idx 1,
        letI := algebraOfHom f (𝒲.inter s)
        ∃ cs : Γ(Ak', Ue') → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(A, 𝒲.inter s))),
          IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(A, 𝒲.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫
              A.homOfLE (𝒲.inter_le s 0) ≫ m (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter f 𝒲 s).isoSpec.inv ≫
              A.homOfLE (𝒲.inter_le s 1) ≫ m (s.1 1))
            fk' Lk' (i₀' ≫ g') Ue' cs ∧
          ∀ (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V), σ s (cs a ξ) = c.1 a ξ s) ∧

      (∀ (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit yk).d (𝒲.comap bk) 1 (c.1 a ξ) = 0) := by sorry
