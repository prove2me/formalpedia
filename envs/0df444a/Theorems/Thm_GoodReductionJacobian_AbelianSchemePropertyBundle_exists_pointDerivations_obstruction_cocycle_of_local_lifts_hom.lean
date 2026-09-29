-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_pointDerivations_obstruction_cocycle_of_local_lifts_hom
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_pointDerivations_obstruction_cocycle_of_local_lifts_hom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/bb46e793-9dea-5bf3-a26d-a0a5cbfcce82
-- title:
--   Obstruction cocycle of local lifts along a small surjection
-- statement:
--   Let $T'$ be an Artinian local ring with algebraically closed residue field $k=\mathrm{ResidueField}\,T'$, let $T$ be a commutative ring, and let $\pi:T'\to T$ be a surjective ring homomorphism whose kernel $I=\ker\pi$ is nilpotent, is contained in $\mathfrak m_{T'}$ and satisfies $I\,\mathfrak m_{T'}=0$; let $\rho:T\to k$ satisfy $\rho\circ\pi=\mathrm{residue}$. Let $V$ be a finite-dimensional $k$-vector space carrying also a $T'$-module structure compatible with the $k$-structure (with the matching right action), and let $\iota:V\to T'$ be an injective $T'$-linear map with image $I$. The data consist of: $f_0:A_0\to\operatorname{Spec} T$ with a commutative relative group law $L_0$ and satisfying `AbelianSchemePropertyBundle T f₀` (smooth, proper, connected fibres, and a relative group law exists); $f:A\to\operatorname{Spec} T'$ smooth, proper and separated, with $g:A_0\to A$ making the square with $\operatorname{Spec}\pi$ cartesian; the same data primed, $f_0',L_0',f',g'$; a section $e'$ of $f'$ over $\operatorname{Spec}T'$ whose base change along $\operatorname{Spec}\pi$ is the unit section of $L_0'$ followed by $g'$; a morphism $u_0:A_0\to A_0'$ over $\operatorname{Spec}T$; an ordered affine cover $\mathcal W$ of $A$ (a finite linearly ordered family of affine opens covering $A$) together with morphisms $m_i:\mathcal W_i\to A'$ over the bases whose restrictions along $g$ agree with $u_0$ followed by $g'$; the fibre $i_0':A_k'\to A_0'$ of $f_0'$ along $\operatorname{Spec}\rho$, with relative group law $L_k'$ over $k$, an affine open $U_{e'}\subseteq A_k'$ and a $k$-point $e_1'$ of $U_{e'}$ whose image in $A_k'$ is the unit of $L_k'$; the fibre $b_k:A_k\to A$ of $f$ along the residue map, $b_k$ affine, with structure map $y_k$, and ring isomorphisms $\sigma_s:k\otimes_{T'}\Gamma(A,\mathcal W_s)\to\Gamma(A_k,(b_k^{-1}\mathcal W)_s)$ for every strictly increasing tuple $s$ of indices, sending $1\otimes x$ to the restriction of $b_k^\ast x$ and $a\otimes 1$ to the image of $a$ under the structure map. The conclusion asserts the existence of a $k$-linear map $c$ from $\Gamma(A_k',U_{e'})$ to $\mathrm{Hom}_k\bigl(V^\vee,\check C^1(b_k^{-1}\mathcal W,\mathcal O)\bigr)$, the degree-one Čech cochains of the structure presheaf of $y_k$, which is a derivation at the evaluation homomorphism $\Gamma(A_k',U_{e'})\to k$ given by $e_1'$, that is $c(ab)=\mathrm{ev}(a)\,c(b)+\mathrm{ev}(b)\,c(a)$, such that: first, for every pair $s=(s_0<s_1)$ there is a map $c_s:\Gamma(A_k',U_{e'})\to\mathrm{Hom}_k(V^\vee,k\otimes_{T'}\Gamma(A,\mathcal W_s))$ which is a system of tangent coordinates for the two morphisms $\operatorname{Spec}\Gamma(A,\mathcal W_s)\to A'$ obtained from the inverse of the canonical isomorphism with $\mathcal W_s=\mathcal W_{s_0}\cap\mathcal W_{s_1}$ followed by the inclusion into $\mathcal W_{s_j}$ and by $m_{s_j}$ ($j=0,1$), in the sense of `IsTangentCoordsOfPairAt` for $I$, $V$, $\iota$, $f_k'$, $L_k'$, $i_0'$ followed by $g'$, and $U_{e'}$: there are a morphism $w_0$ from the spectrum of the thickening $(k\otimes_{T'}\Gamma(A,\mathcal W_s))\otimes_k(k\oplus V)$ to $A_k'$ over the canonical base morphism such that $w_0$ followed by $i_0'\,g'$ is a tangent of the pair, i.e. factors as a Schlessinger homomorphism out of the pair ring of $I$ followed by a morphism whose two projections are the two given maps, and a morphism $w_1$ into $U_{e'}$ lifting the $L_k'$-translate of $w_0$ to the unit, with $c_s$ the tangent coordinates of the induced homomorphism $\Gamma(A_k',U_{e'})\to$ thickening; moreover $\sigma_s(c_s(a)(\xi))=c(a)(\xi)(s)$ for all $a$ and all $\xi\in V^\vee$; secondly, the Čech differential of $c(a)(\xi)$ vanishes for all $a$ and $\xi$.
--
--   This is the construction of the obstruction class to gluing chartwise lifts of a morphism of abelian schemes along a small surjection: two lifts over an overlap differ by a derivation with values in $I$ tensored with the pullback of the tangent sheaf of the target, which for an abelian scheme is trivialised by the tangent space at the unit, and the resulting degree-one Čech cochain is shown to be a cocycle. It is used in the deformation-theoretic step that lifts morphisms of abelian schemes, and is cited by the `BareDeformation` results on existence of compatible lifts and on the vanishing of the associated obstruction class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_pointDerivations_obstruction_cocycle_of_local_lifts_hom.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_pointDerivations_obstruction_cocycle_of_local_lifts_hom
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
