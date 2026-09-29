-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_pointDerivations_obstruction_cocycle_of_local_lifts
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_pointDerivations_obstruction_cocycle_of_local_lifts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/2687e840-f0b9-50f5-b345-2211dbf0fe39
-- title:
--   Obstruction cocycle for local lifts of the group law
-- statement:
--   Fix a universe-$u$ Artinian local ring $T'$ with algebraically closed residue field $k=\mathrm{ResidueField}\,T'$, a commutative ring $T$ and a surjective ring map $\pi\colon T'\to T$ whose kernel $I=\ker\pi$ is nilpotent, satisfies $I\cdot\mathfrak m_{T'}=0$ and $I\subseteq\mathfrak m_{T'}$; let $\rho\colon T\to k$ satisfy $\rho\circ\pi=\mathrm{residue}$, and let $V$ be a finite-dimensional $k$-space, also a $T'$-module compatibly, together with an injective $T'$-linear $\iota\colon V\to T'$ whose range is $I$. Let $f_0\colon A_0\to\operatorname{Spec}T$ carry a commutative relative group law $L_0$ (functorial $\mathrm{mul}$, $\mathrm{one}$, $\mathrm{inv}$ on sections over varying bases, with associativity, unit, inverse and base-change naturality) and satisfy `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, a relative group law exists); let $f\colon A\to\operatorname{Spec}T'$ be smooth and proper, $g\colon A_0\to A$ cartesian over $\operatorname{Spec}\pi$, and $e$ a section of $f$ whose reduction along $\pi$ is the unit of $L_0$ composed with $g$, with $\mathrm{pullback.fst}\,f\,f\gg f$ separated. Fix a finite ordered affine open cover $\mathcal W$ of $A\times_{T'}A$, maps $m_i\colon \mathcal W_i\to A$ over the base which on the fibre over $T$ restrict to $g$ composed with the multiplication $\mu_0$ of $L_0$; a special fibre $f_k\colon A_k\to\operatorname{Spec}k$ of $f_0$ along $\rho$ with some relative group law $L_k$, an affine open $U_e\subseteq A_k$ and a $k$-point $e_1$ of $U_e$ whose composite into $A_k$ is the unit of $L_k$; a special fibre $b_k\colon P_k\to A\times_{T'}A$ along the residue map with $b_k$ affine, together with ring isomorphisms $\sigma_s\colon k\otimes_{T'}\Gamma(A\times_{T'}A,\mathcal W_s)\cong\Gamma(P_k,(b_k^{-1}\mathcal W)_s)$ for all simplices $s$, pinned on $1\otimes x$ (restriction of $b_k^{\ast}$) and on $a\otimes 1$ (the structure map); projections $p_1,p_2\colon P_k\to A_k$ exhibiting $P_k$ as $A_k\times_k A_k$ and compatible with $b_k$ and the two projections; a $k$-point $e_k$ of $A_k$ lifting $e$; and closed immersions $i_X,i_Y\colon A_k\to P_k$ realising $(\mathrm{id},e_k)$ and $(e_k,\mathrm{id})$, compatible with $b_k$ and the two sections $(\mathrm{id}_A,f\gg e.1)$, $(f\gg e.1,\mathrm{id}_A)$ of $A\times_{T'}A$. The conclusion asserts the existence of a $k$-linear map $c$ on $\Gamma(A_k,U_e)$ with values in $\mathrm{Hom}_k(V^{\vee},\,$degree-$1$ Čech cochains of the structure-sheaf $\mathcal O$-module presheaf of $P_k$ for the cover $b_k^{-1}\mathcal W)$ which is a point derivation at the unit, i.e. $c(ab)=\mathrm{ev}(a)c(b)+\mathrm{ev}(b)c(a)$ for the evaluation $\Gamma(A_k,U_e)\to k$ induced by $e_1$, such that: (i) for every $1$-simplex $s$ of $\mathcal W$ there is a map $c_s$ from $\Gamma(A_k,U_e)$ to $\mathrm{Hom}_k(V^{\vee},k\otimes_{T'}\Gamma(A\times_{T'}A,\mathcal W_s))$ which is a system of tangent coordinates, in the sense of `IsTangentCoordsOfPairAt`, for the pair of maps on $\mathcal W_s$ obtained from $m_{s(0)}$ and $m_{s(1)}$ — that is, there are a thickened point $w_0$ of $A_k$ over the thickening of $\Gamma$ by $V$ whose composite with $i_0\gg g$ is a tangent vector of that pair in the sense of `IsTangentOfPair`, a factorisation $w_1$ through $U_e$ of the $L_k$-translate of $w_0$ to the unit, and $c_s$ is `tangentCoords` of the associated chart ring map — and $\sigma_s(c_s(a)(\xi))=c(a)(\xi)(s)$ for all $a$ and $\xi\in V^{\vee}$; (ii) the Čech differential of $c(a)(\xi)$ vanishes; (iii) the pullback of $c(a)(\xi)$ along $i_X$, and likewise (iv) along $i_Y$, is the Čech differential of a $0$-cochain on $A_k$ for the cover $i_X^{-1}b_k^{-1}\mathcal W$, respectively $i_Y^{-1}b_k^{-1}\mathcal W$.
--
--   This constructs the obstruction datum attached to a family of local lifts of the multiplication of an abelian scheme across a small extension $T'\to T$: the discrepancies of the lifts on overlaps are recorded as a Čech $1$-cocycle with values in tangent coordinates, depending on sections near the unit as a point derivation, and trivial along the two unit slices. It is used by [`GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_isPullback_of_ker_mul_maximalIdeal_eq_bot`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_isPullback_of_ker_mul_maximalIdeal_eq_bot), which globalises the local lifts to a group law on the deformation $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_pointDerivations_obstruction_cocycle_of_local_lifts.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_pointDerivations_obstruction_cocycle_of_local_lifts
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (hc₀ : L₀.IsCommutative)
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of T'))) f)
    (he : Spec.map (CommRingCat.ofHom π) ≫ e.1 = (L₀.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ g)

    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

    [IsSeparated (pullback.fst f f ≫ f)]
    (𝒲 : (pullback f f).OrderedAffineCover)
    (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A)
    (hmf : ∀ i, m i ≫ f = (𝒲.U i).ι ≫ pullback.fst f f ≫ f)
    (hmμ : ∀ i, morphismRestrict (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) (𝒲.U i) ≫ m i
        = ((pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ⁻¹ᵁ (𝒲.U i)).ι ≫
          (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g)

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

    {Pk : Scheme.{u}} (bk : Pk ⟶ pullback f f) [IsAffineHom bk] (yk : Pk ⟶ Spec (CommRingCat.of (ResidueField T')))
    (hbk : IsPullback bk yk (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom (residue T'))))
    (σ : ∀ {n : ℕ} (s : 𝒲.Idx n),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      ((ResidueField T') ⊗[T'] Γ(pullback f f, 𝒲.inter s)) ≃+* Γ(Pk, (𝒲.comap bk).inter s))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒲.Idx n) (x : Γ(pullback f f, 𝒲.inter s)),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      σ s ((1 : ResidueField T') ⊗ₜ[T'] x) =
        (Pk.presheaf.map (homOfLE (𝒲.comap_inter_le bk s)).op).hom ((bk.app (𝒲.inter s)).hom x))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒲.Idx n) (a : ResidueField T'),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      letI := algebraOfHom yk ((𝒲.comap bk).inter s)
      σ s (a ⊗ₜ[T'] (1 : Γ(pullback f f, 𝒲.inter s))) = algebraMap (ResidueField T') Γ(Pk, (𝒲.comap bk).inter s) a)

    (p₁ p₂ : Pk ⟶ Ak)
    (hp₁ : p₁ ≫ i₀ ≫ g = bk ≫ pullback.fst f f) (hp₁k : p₁ ≫ fk = yk)
    (hp₂ : p₂ ≫ i₀ ≫ g = bk ≫ pullback.snd f f) (hp₂k : p₂ ≫ fk = yk)
    (hPk : IsPullback p₁ p₂ fk fk)
    (ek : Spec (CommRingCat.of (ResidueField T')) ⟶ Ak)
    (hek : ek ≫ i₀ ≫ g = Spec.map (CommRingCat.ofHom (residue T')) ≫ e.1) (hekk : ek ≫ fk = 𝟙 _)
    (iX : Ak ⟶ Pk) [IsClosedImmersion iX] (hiX₁ : iX ≫ p₁ = 𝟙 Ak) (hiX₂ : iX ≫ p₂ = fk ≫ ek)
    (hiXP : iX ≫ bk = (i₀ ≫ g) ≫ pullback.lift (𝟙 A) (f ≫ e.1) (by rw [Category.id_comp, Category.assoc, e.2, Category.comp_id]))
    (iY : Ak ⟶ Pk) [IsClosedImmersion iY] (hiY₁ : iY ≫ p₁ = fk ≫ ek) (hiY₂ : iY ≫ p₂ = 𝟙 Ak)
    (hiYP : iY ≫ bk = (i₀ ≫ g) ≫ pullback.lift (f ≫ e.1) (𝟙 A) (by rw [Category.id_comp, Category.assoc, e.2, Category.comp_id])) :
    letI := algebraOfHom fk Ue
    ∃ c : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit (p₁ ≫ fk)).cochain (𝒲.comap bk) 1)),
      (∀ s : 𝒲.Idx 1,
        letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
        ∃ cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(pullback f f, 𝒲.inter s))),
          IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(pullback f f, 𝒲.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
              (pullback f f).homOfLE (𝒲.inter_le s 0) ≫ m (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
              (pullback f f).homOfLE (𝒲.inter_le s 1) ≫ m (s.1 1))
            fk Lk (i₀ ≫ g) Ue cs ∧
          ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ s (cs a ξ) = c.1 a ξ s) ∧
      (∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit (p₁ ≫ fk)).d (𝒲.comap bk) 1 (c.1 a ξ) = 0) ∧
      (∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        ∃ b : (OModulePresheaf.unit fk).cochain ((𝒲.comap bk).comap iX) 0,
          (OModulePresheaf.unit fk).d ((𝒲.comap bk).comap iX) 0 b = fun t =>
            (Ak.presheaf.map (homOfLE ((𝒲.comap bk).comap_inter_le iX t)).op).hom
              ((iX.app ((𝒲.comap bk).inter t)).hom (c.1 a ξ t))) ∧
      (∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        ∃ b : (OModulePresheaf.unit fk).cochain ((𝒲.comap bk).comap iY) 0,
          (OModulePresheaf.unit fk).d ((𝒲.comap bk).comap iY) 0 b = fun t =>
            (Ak.presheaf.map (homOfLE ((𝒲.comap bk).comap_inter_le iY t)).op).hom
              ((iY.app ((𝒲.comap bk).inter t)).hom (c.1 a ξ t))) := by sorry
