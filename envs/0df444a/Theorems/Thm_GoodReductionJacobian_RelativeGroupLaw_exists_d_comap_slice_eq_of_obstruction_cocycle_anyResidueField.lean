-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_d_comap_slice_eq_of_obstruction_cocycle_anyResidueField
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_d_comap_slice_eq_of_obstruction_cocycle_anyResidueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/7a0e5836-e39c-5ed2-9c14-43edc553b813
-- title:
--   Slice restrictions of the obstruction cocycle are coboundaries
-- statement:
--   Let $T'$ be an artinian local ring and $\pi\colon T'\to T$ a surjective ring map with nilpotent kernel satisfying $\ker\pi\cdot\mathfrak m_{T'}=0$ and $\ker\pi\subseteq\mathfrak m_{T'}$, and let $\rho\colon T\to\kappa:=\mathrm{ResidueField}\,T'$ satisfy $\rho\circ\pi=\mathrm{residue}$. Let $f_0\colon A_0\to\operatorname{Spec}T$ carry a commutative relative group law $L_0$ and satisfy `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, a relative group law exists), let $f\colon A\to\operatorname{Spec}T'$ be smooth and proper, let $g\colon A_0\to A$ exhibit $f_0$ as the base change of $f$ along $\operatorname{Spec}\pi$, and let $e$ be a section of $f$ whose reduction along $\pi$ is the unit of $L_0$ followed by $g$. Let $V$ be a finite-dimensional $\kappa$-vector space with compatible $T'$-action and $\iota\colon V\to T'$ an injective $T'$-linear map with image $\ker\pi$. Let $\mathcal W$ be a finite ordered affine cover of $P=A\times_{T'}A$ (affine opens $U_i$ indexed by a linearly ordered finite set, covering $P$) together with morphisms $m_i\colon U_i\to A$ over $T'$ which, restricted to the preimage of $U_i$ in $A_0\times_TA_0$, agree with the multiplication $L_0.\mathrm{mul}$ of the two projections followed by $g$; $\mathrm{pr}_1\circ f$ is assumed separated. On the special fibre, $f_k\colon A_k\to\operatorname{Spec}\kappa$ carries a relative group law $L_k$, $i_0$ exhibits $f_k$ as the base change of $f_0$ along $\operatorname{Spec}\rho$, $U_e\subseteq A_k$ is an affine open and $e_1\colon\operatorname{Spec}\kappa\to U_e$ is the unit of $L_k$; $b_k\colon P_k\to P$ is an affine morphism exhibiting $y_k$ as the base change of $\mathrm{pr}_1\circ f$ along $\operatorname{Spec}(\mathrm{residue})$, with ring isomorphisms $\sigma_s\colon\kappa\otimes_{T'}\Gamma(P,\mathcal W_s)\xrightarrow{\sim}\Gamma(P_k,(b_k^{-1}\mathcal W)_s)$ on all intersections $\mathcal W_s$ of chains of the cover, compatible with $1\otimes x\mapsto b_k^{*}x$ and with the $\kappa$-algebra structures. Morphisms $p_1,p_2\colon P_k\to A_k$ over $\kappa$ lie over $b_k\circ\mathrm{pr}_1$, $b_k\circ\mathrm{pr}_2$ and exhibit $P_k=A_k\times_\kappa A_k$; $e_k$ is a $\kappa$-point of $A_k$ lifting $e$, and the closed immersions $i_X,i_Y\colon A_k\to P_k$ are the slices $(\mathrm{id},f_k\circ e_k)$ and $(f_k\circ e_k,\mathrm{id})$, lying over the sections $(\mathrm{id}_A,f\circ e)$ and $(f\circ e,\mathrm{id}_A)$ of $P$ composed with $i_0\circ g$. Finally, let $c$ be a $\kappa$-point derivation of $\Gamma(A_k,U_e)$ at the unit (evaluation through $e_1$) with values in $\mathrm{Hom}_\kappa(V^{\vee},C^1(b_k^{-1}\mathcal W,\mathcal O_{P_k}))$, and assume that for every chain $s$ of length one there are maps $c_s\colon\Gamma(A_k,U_e)\to\mathrm{Hom}_\kappa(V^\vee,\kappa\otimes_{T'}\Gamma(P,\mathcal W_s))$ satisfying `IsTangentCoordsOfPairAt` for the ideal $\ker\pi$, the module $V$ with $\iota$, the ring $\Gamma(P,\mathcal W_s)$ and the two morphisms $\operatorname{Spec}\Gamma(P,\mathcal W_s)\to P\to A$ obtained from $m$ at the two indices of $s$ — that is, there are a thickened point $w_0$ of $A_k$ over the base and a lift $w_1$ into $U_e$ such that $w_0$ followed by $i_0\circ g$ is a common tangent of that pair of morphisms, $w_1$ is the $L_k$-translate of $w_0$ to the unit, and $c_s$ is the tangent-coordinate map of the chart ring homomorphism of $w_1$ — and such that $\sigma_s(c_s(a)(\xi))=c(a)(\xi)_s$ for all $a,\xi$. The conclusion is twofold: for every $a\in\Gamma(A_k,U_e)$ and $\xi\in V^\vee$, the $1$-cochain on $A_k$ for the cover $i_X^{-1}b_k^{-1}\mathcal W$ obtained by restricting $i_X^{*}(c(a)(\xi)_t)$ is the Čech differential $d^0b$ of a $0$-cochain $b$ with values in the structure presheaf of $A_k$ over $f_k$, and the same holds with $i_Y$ in place of $i_X$.
--
--   This is the rigidity step in the construction of the obstruction cocycle for lifting a relative group law along a small extension $T'\to T$: along the two slices $A\times e$ and $e\times A$ the multiplication lifting problem is solved globally by the identity, so the tangent-coordinate $1$-cochain restricts to a coboundary on each slice. It is used by [`GoodReductionJacobian.RelativeGroupLaw.exists_pointDerivations_obstruction_cocycle_of_local_lifts_anyResidueField`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_pointDerivations_obstruction_cocycle_of_local_lifts_anyResidueField), which assembles the local lifts $m_i$ into a well-defined obstruction class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_d_comap_slice_eq_of_obstruction_cocycle_anyResidueField.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_d_comap_slice_eq_of_obstruction_cocycle_anyResidueField
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
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
    (hiYP : iY ≫ bk = (i₀ ≫ g) ≫ pullback.lift (f ≫ e.1) (𝟙 A) (by rw [Category.id_comp, Category.assoc, e.2, Category.comp_id]))
    (c : letI := algebraOfHom fk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit (p₁ ≫ fk)).cochain (𝒲.comap bk) 1)))
    (hc : letI := algebraOfHom fk Ue
      (∀ s : 𝒲.Idx 1,
        letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
        ∃ cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(pullback f f, 𝒲.inter s))),
          IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(pullback f f, 𝒲.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
              (pullback f f).homOfLE (𝒲.inter_le s 0) ≫ m (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
              (pullback f f).homOfLE (𝒲.inter_le s 1) ≫ m (s.1 1))
            fk Lk (i₀ ≫ g) Ue cs ∧
          ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ s (cs a ξ) = c.1 a ξ s)) :
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
