-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_lift_of_pointDerivations_coboundary
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_lift_of_pointDerivations_coboundary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/45471d4d-0bad-51c0-b617-f8a1d8e9553a
-- title:
--   Lifting a morphism whose obstruction cochain is a coboundary
-- statement:
--   Let $T'$ be an artinian local ring with algebraically closed residue field $k=\mathrm{ResidueField}\,T'$, let $\pi:T'\to T$ be a surjective ring homomorphism whose kernel is nilpotent and satisfies $(\ker\pi)\cdot\mathfrak m_{T'}=0$ and $\ker\pi\subseteq\mathfrak m_{T'}$, and let $\rho:T\to k$ satisfy $\rho\circ\pi=\mathrm{residue}$. On the source side, $f_0:A_0\to\operatorname{Spec}T$ carries a commutative relative group law $L_0$ and satisfies `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, a relative group law exists), $f:A\to\operatorname{Spec}T'$ is smooth, proper and separated, and $g:A_0\to A$ exhibits $f_0$ as the pullback of $f$ along $\operatorname{Spec}\pi$; the primed data $f_0',L_0',h_0',f',g'$ are of the same shape, together with a section $e'$ of $f'$ over $\operatorname{Spec}T'$ whose composite $\operatorname{Spec}\pi$ followed by $e'$ equals the unit section of $L_0'$ followed by $g'$. Given $u_0:A_0\to A_0'$ over $T$, a finite-dimensional $k$-vector space $V$ with compatible $T'$-module and central right $k$-actions and an injective $T'$-linear $\iota:V\to T'$ with image $\ker\pi$, let $\mathcal W$ be a finite ordered cover of $A$ by affine opens and let $m_i:\mathcal W.U\,i\to A'$ be morphisms over $f$ (i.e. $m_i$ followed by $f'$ is the inclusion followed by $f$) whose restrictions along $g$ agree with $u_0$ followed by $g'$. Let $f_k':A_k'\to\operatorname{Spec}k$ with relative group law $L_k'$ be the pullback of $f_0'$ along $\operatorname{Spec}\rho$ via $i_0'$, let $U_{e'}$ be an affine open of $A_k'$ and $e_1':\operatorname{Spec}k\to U_{e'}$ a lift of the unit of $L_k'$, and let $b_k:A_k\to A$ be the affine pullback of $f$ along $\operatorname{Spec}(\mathrm{residue}\,T')$ with structure map $y_k$, together with ring isomorphisms $\sigma_s:k\otimes_{T'}\Gamma(A,\mathcal W.\mathrm{inter}\,s)\cong\Gamma(A_k,(\mathcal W.\mathrm{comap}\,b_k).\mathrm{inter}\,s)$ compatible with the two structure maps ($\sigma_s(1\otimes x)$ is the restriction of $b_k^\sharp x$, and $\sigma_s(a\otimes1)$ is $a$ via the structure map). Finally let $c$ be a point derivation of $\Gamma(A_k',U_{e'})$ at the evaluation homomorphism determined by $e_1'$ — a $k$-linear map $D$ with $D(ab)=\mathrm{ev}(a)D(b)+\mathrm{ev}(b)D(a)$ — with values in $k$-linear maps from the dual of $V$ to the $1$-cochains of the structure-sheaf $\mathcal O$-module presheaf `OModulePresheaf.unit` $y_k$ on the pulled-back cover $\mathcal W.\mathrm{comap}\,b_k$, subject to: for every strictly increasing pair $s$ of indices there are coordinates $c_s$ on $\Gamma(A_k',U_{e'})$, valued in $k$-linear maps from the dual of $V$ to $k\otimes_{T'}\Gamma(A,\mathcal W.\mathrm{inter}\,s)$, which are tangent coordinates in the sense of `IsTangentCoordsOfPairAt` for the ideal $\ker\pi$, $V$, $\iota$ and the pair of morphisms obtained from $m_{s(0)}$ and $m_{s(1)}$ on the affine open $\mathcal W.\mathrm{inter}\,s$, relative to $f_k'$, $L_k'$, $i_0'$ followed by $g'$ and $U_{e'}$, and which correspond to $c$ in the component $s$ under $\sigma_s$. Assume moreover that $c$ is the Čech coboundary of a point derivation $b$ of the same kind with values in $0$-cochains, that is $d(b(a)(\xi))=c(a)(\xi)$ for all $a\in\Gamma(A_k',U_{e'})$ and all $\xi$ in the dual of $V$. Then there exists $u:A\to A'$ with $u$ followed by $f'$ equal to $f$ and $g$ followed by $u$ equal to $u_0$ followed by $g'$.
--
--   This is the gluing step in the deformation theory of a morphism of abelian schemes across a small surjection $T'\to T$: the local lifts $m_i$ of $u_0$ on the members of an affine cover, corrected by the $0$-cochain $b$ whose coboundary is the obstruction $1$-cochain $c$, patch to a global lift $u$ of $u_0$ over $T'$. It is used to prove the criterion `exists_hom_lift_iff_forall_mem_range_d_of_local_lifts`, which expresses liftability of a morphism by the vanishing of the class of the obstruction cochain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_lift_of_pointDerivations_coboundary.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_lift_of_pointDerivations_coboundary
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
    (b : letI := algebraOfHom fk' Ue'
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak', Ue')
          ((Ue'.topIso.inv ≫ e₁'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit yk).cochain (𝒲.comap bk) 0)))
    (hb : letI := algebraOfHom fk' Ue'
      ∀ (a : Γ(Ak', Ue')) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit yk).d (𝒲.comap bk) 0 (b.1 a ξ) = c.1 a ξ) :
    ∃ u : A ⟶ A', u ≫ f' = f ∧ g ≫ u = u₀ ≫ g' := by sorry
