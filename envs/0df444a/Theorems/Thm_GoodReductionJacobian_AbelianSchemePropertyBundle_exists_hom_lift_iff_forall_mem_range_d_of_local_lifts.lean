-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_lift_iff_forall_mem_range_d_of_local_lifts
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_lift_iff_forall_mem_range_d_of_local_lifts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/f22a7fd8-9b85-5b78-b33f-9f3eda303472
-- title:
--   Morphism lifts iff its obstruction cochain is a coboundary
-- statement:
--   Let $T'$ be an artinian local ring whose residue field $\kappa = \mathrm{ResidueField}\,T'$ is algebraically closed, let $T$ be a commutative ring and $\pi : T' \to T$ a surjection whose kernel is nilpotent, satisfies $(\ker \pi)\cdot \mathfrak m_{T'} = 0$ and is contained in $\mathfrak m_{T'}$; let $\rho : T \to \kappa$ satisfy $\rho \circ \pi = \mathrm{residue}$. Data: $f_0 : A_0 \to \operatorname{Spec} T$ and $f_0' : A_0' \to \operatorname{Spec} T$, each carrying a commutative relative group law and satisfying `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, a relative group law exists); smooth proper separated $f : A \to \operatorname{Spec} T'$ and $f' : A' \to \operatorname{Spec} T'$ with $g, g'$ exhibiting $f_0, f_0'$ as the base changes along $\operatorname{Spec} \pi$; a section $e'$ of $f'$ reducing to the unit section of $L_0'$ composed with $g'$; a morphism $u_0 : A_0 \to A_0'$ over $T$. Further: a finite-dimensional $\kappa$-vector space $V$, also a $T'$-module compatibly, and an injective $T'$-linear $\iota : V \to T'$ with image $\ker \pi$; an ordered affine cover $\mathcal W$ of $A$ (finitely many affine opens indexed by a linear order, covering $A$) together with local lifts $m_i : \mathcal W_i \to A'$ over $T'$ agreeing with $u_0$ after reduction; the special fibre $f_k' : A_k' \to \operatorname{Spec} \kappa$ of $f_0'$ along $\operatorname{Spec} \rho$ with a relative group law $L_k'$, an affine open $U_{e'} \subseteq A_k'$ and a $\kappa$-point $e_1'$ of it equal to the unit section of $L_k'$; the special fibre $b_k : A_k \to A$ of $f$ over $\kappa$ (an affine morphism), with ring isomorphisms $\sigma_s : \kappa \otimes_{T'} \Gamma(A, \mathcal W_s) \cong \Gamma(A_k, (b_k^{-1}\mathcal W)_s)$ on all intersections $\mathcal W_s$ over strictly increasing index tuples, compatible with $b_k^{\ast}$ on $1 \otimes x$ and with the structure map on $a \otimes 1$. Finally $c$ is a derivation of $\Gamma(A_k', U_{e'})$ at the point $e_1'$ (a $\kappa$-linear map satisfying the Leibniz rule with respect to evaluation at $e_1'$) with values in $\kappa$-linear maps from $\mathrm{Dual}_\kappa V$ to the Čech $1$-cochains of the structure presheaf of $A_k$ for the cover $b_k^{-1}\mathcal W$, and it is assumed that for each pair $s$ of indices there is a family $c_s$ of tangent coordinates of the pair of morphisms obtained from $\mathcal W_s \to \mathcal W_{s(0)} \xrightarrow{m} A'$ and $\mathcal W_s \to \mathcal W_{s(1)} \xrightarrow{m} A'$, in the sense of `IsTangentCoordsOfPairAt` for $\ker\pi$, $V$, $\iota$, $\Gamma(A,\mathcal W_s)$, $f_k'$, $L_k'$, $i_0' \gg g'$ and $U_{e'}$, whose image under $\sigma_s$ is the $s$-component of $c$. The conclusion is an equivalence: a morphism $u : A \to A'$ with $u \gg f' = f$ and $g \gg u = u_0 \gg g'$ exists if and only if for every $a \in \Gamma(A_k', U_{e'})$ and every $\xi \in \mathrm{Dual}_\kappa V$ the $1$-cochain $c(a)(\xi)$ lies in the image of the Čech differential $d^0$ of `OModulePresheaf.unit y_k` for the cover $b_k^{-1}\mathcal W$.
--
--   This is the obstruction criterion for lifting a morphism of abelian schemes along a small extension of artinian local rings: the class of the derivation-valued Čech $1$-cochain recording the discrepancies between given local lifts vanishes in $H^1$ exactly when a global lift exists. It is used in the deformation-theoretic part of the construction of Néron models and good-reduction Jacobians, being invoked by the regluing statement [`GoodReductionJacobian.BareDeformation.exists_comp_eq_comp_iff_forall_mem_range_d_of_isRegluingBy_of_twisted_local_lifts_bare`](thm.html#GoodReductionJacobian.BareDeformation.exists_comp_eq_comp_iff_forall_mem_range_d_of_isRegluingBy_of_twisted_local_lifts_bare); the implication from coboundaries to lifts is supplied by `exists_hom_lift_of_pointDerivations_coboundary`, and the converse uses the comparison of two systems of local lifts in `exists_d_eq_obstruction_cocycle_sub_of_local_lifts_hom`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_lift_iff_forall_mem_range_d_of_local_lifts.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_lift_iff_forall_mem_range_d_of_local_lifts
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
    :
    letI := algebraOfHom fk' Ue'
    (∃ u : A ⟶ A', u ≫ f' = f ∧ g ≫ u = u₀ ≫ g') ↔
      ∀ (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V),
        c.1 a ξ ∈ LinearMap.range ((OModulePresheaf.unit yk).d (𝒲.comap bk) 0) := by sorry
