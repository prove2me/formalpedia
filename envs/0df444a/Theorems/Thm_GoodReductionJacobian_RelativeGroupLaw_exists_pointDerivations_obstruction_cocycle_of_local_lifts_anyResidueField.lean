-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_pointDerivations_obstruction_cocycle_of_local_lifts_anyResidueField
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_pointDerivations_obstruction_cocycle_of_local_lifts_anyResidueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/32a08b44-383f-5c05-87c5-4cf96a918e91
-- title:
--   Obstruction cocycle for local lifts of the group law
-- statement:
--   Let $\pi\colon T'\to T$ be a surjection of commutative rings with $T'$ Artinian local, with nilpotent kernel $I=\ker\pi$ satisfying $I\cdot\mathfrak m_{T'}=0$ and $I\subseteq\mathfrak m_{T'}$. Let $f_0\colon A_0\to\operatorname{Spec}T$ carry a relative group law $L_0$ that is commutative, together with the bundle `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, a group law), and let $f\colon A\to\operatorname{Spec}T'$ be smooth and proper with a cartesian square $g\colon A_0\to A$ over $\operatorname{Spec}\pi$ and a section $e$ of $f$ whose reduction along $\pi$ is the unit of $L_0$ followed by $g$. Fix a $T$-algebra map $\rho\colon T\to k:=\operatorname{ResidueField}T'$ with $\rho\circ\pi$ the residue map, and a presentation of $I$ by a finite $k$-vector space $V$: an injective $T'$-linear $\iota\colon V\to T'$ with image $I$. Assume $A\times_{T'}A$ separated over $\operatorname{Spec}T'$, and fix a finite ordered affine open cover $\mathcal W$ of $A\times_{T'}A$ with, for each index $i$, a morphism $m_i\colon \mathcal W_i\to A$ over $\operatorname{Spec}T'$ whose reduction along the map $A_0\times_T A_0\to A\times_{T'}A$ agrees with $L_0$-multiplication followed by $g$. Fix further: a special fibre $f_k\colon A_k\to\operatorname{Spec}k$ of $f_0$ along $\rho$ (cartesian, via $i_0$) with some relative group law $L_k$, an affine open $U_e\subseteq A_k$ and $e_1\colon\operatorname{Spec}k\to U_e$ whose composite with the inclusion is the unit of $L_k$; a special fibre $b_k\colon P_k\to A\times_{T'}A$ along the residue map, affine, with structure map $y_k$, together with $k$-algebra isomorphisms $\sigma_s\colon k\otimes_{T'}\Gamma(A\times_{T'}A,\mathcal W_s)\cong\Gamma(P_k,(b_k^{-1}\mathcal W)_s)$ on all simplices $s$, normalised on pure tensors $1\otimes x$ and $a\otimes 1$; projections $p_1,p_2\colon P_k\to A_k$ exhibiting $P_k$ as $A_k\times_k A_k$ and compatible with the two projections of $A\times_{T'}A$ through $i_0\circ g$; a unit section $e_k$ of $f_k$ lifting $\operatorname{Spec}(\text{residue})\circ e$; and closed immersions $i_X,i_Y\colon A_k\to P_k$ with $(p_1i_X,p_2i_X)=(\mathrm{id},f_ke_k)$, $(p_1i_Y,p_2i_Y)=(f_ke_k,\mathrm{id})$, lying over $(\mathrm{id}_A,f\circ e)$ and $(f\circ e,\mathrm{id}_A)$ respectively. The conclusion asserts the existence of a $k$-linear map $c$ from $\Gamma(A_k,U_e)$ to $\operatorname{Hom}_k(V^\vee,\ \check C^1(b_k^{-1}\mathcal W,\mathcal O))$ satisfying the Leibniz rule $c(ab)=\mathrm{ev}(a)c(b)+\mathrm{ev}(b)c(a)$ for the evaluation homomorphism $\Gamma(A_k,U_e)\to k$ determined by $e_1$, where $\check C^1$ denotes degree-one Čech cochains of the structure-sheaf $O$-module presheaf of $p_1\circ f_k$ on the cover $b_k^{-1}\mathcal W$ of $P_k$, such that: (i) for every $1$-simplex $s$ there are maps $c_s$ from $\Gamma(A_k,U_e)$ to $\operatorname{Hom}_k(V^\vee,k\otimes_{T'}\Gamma(A\times_{T'}A,\mathcal W_s))$ which are tangent coordinates, in the sense of `IsTangentCoordsOfPairAt` for the data $(I,V,\iota)$, of the pair of morphisms $\operatorname{Spec}\Gamma(A\times_{T'}A,\mathcal W_s)\to A$ obtained from $m_{s(0)}$ and $m_{s(1)}$ on the overlap, relative to $f_k$, $L_k$, $i_0\circ g$ and $U_e$, and $\sigma_s\circ c_s=c$ componentwise; (ii) each $c(a)(\xi)$ is a Čech cocycle, $d\,c(a)(\xi)=0$; (iii) the pullback of $c(a)(\xi)$ along $i_X$ is a Čech coboundary on the cover $(b_k^{-1}\mathcal W)$ pulled back along $i_X$; (iv) the same holds along $i_Y$.
--
--   This produces the obstruction class to lifting the group law of an abelian scheme along a small extension: the local lifts $m_i$ of the multiplication differ on overlaps by tangent vectors, and these differences are assembled into a derivation-valued Čech $1$-cocycle, normalised by the vanishing (up to coboundary) of its restrictions to the two unit slices. It is the input to [`GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_smallExtension`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_smallExtension), where the cocycle is shown to be a coboundary and the local lifts are thereby glued to a global multiplication.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_pointDerivations_obstruction_cocycle_of_local_lifts_anyResidueField.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_pointDerivations_obstruction_cocycle_of_local_lifts_anyResidueField
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
