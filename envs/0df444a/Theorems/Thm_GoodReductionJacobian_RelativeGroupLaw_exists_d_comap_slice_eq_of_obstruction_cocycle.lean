-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_d_comap_slice_eq_of_obstruction_cocycle
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_d_comap_slice_eq_of_obstruction_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/020ad35e-d7a6-5508-92f8-c51697c678ed
-- title:
--   Slice restrictions of the obstruction cocycle are coboundaries
-- statement:
--   Let $T'$ be an Artinian local ring with algebraically closed residue field $k$, let $T$ be a commutative ring and $\pi\colon T'\to T$ a surjective homomorphism whose kernel $I$ is nilpotent, satisfies $I\cdot\mathfrak m_{T'}=0$ and $I\subseteq\mathfrak m_{T'}$, and let $\rho\colon T\to k$ satisfy $\rho\circ\pi=\mathrm{residue}$. Let $V$ be a finite-dimensional $k$-vector space, compatibly a $T'$-module, and $\iota\colon V\to T'$ an injective $T'$-linear map with image $I$. Let $f_0\colon A_0\to\operatorname{Spec}T$ carry a commutative relative group law $L_0$ and satisfy `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, admitting a relative group law); let $f\colon A\to\operatorname{Spec}T'$ be smooth and proper, $g$ exhibit $A_0$ as the base change of $A$ along $\operatorname{Spec}\pi$, and $e$ a section of $f$ whose reduction is the unit section of $L_0$ composed with $g$. Assume $A\times_{T'}A$ is separated over $T'$, and fix an ordered affine cover $\mathcal W$ of it with morphisms $m_i\colon W_i\to A$ over $T'$ whose restrictions to the special fibre agree with the $L_0$-multiplication followed by $g$. On the special fibre: $f_k\colon A_k\to\operatorname{Spec}k$ with relative group law $L_k$, $i_0$ exhibiting $A_k$ as base change of $A_0$ along $\operatorname{Spec}\rho$, an affine open $U_e$ through which the unit of $L_k$ factors via $e_1$; an affine $b_k\colon P_k\to A\times_{T'}A$ exhibiting $P_k$ over $k$ as the special fibre, with ring isomorphisms $\sigma_s\colon k\otimes_{T'}\Gamma(A\times_{T'}A,W_s)\cong\Gamma(P_k,(\mathcal W.\mathrm{comap}\,b_k).\mathrm{inter}\,s)$ compatible with $b_k$ on sections and with the structure map of $k$; morphisms $p_1,p_2$ over $k$ compatible with $b_k$ and the two projections and making $P_k=A_k\times_kA_k$; a section $e_k$ of $f_k$ lifting $e$; and closed immersions $i_X,i_Y\colon A_k\to P_k$ with $i_X\circ(p_1,p_2)=(\mathrm{id},f_k\circ e_k)$, $i_Y\circ(p_1,p_2)=(f_k\circ e_k,\mathrm{id})$, lying over the slices $(\mathrm{id}_A,f\circ e)$ and $(f\circ e,\mathrm{id}_A)$ of $A\times_{T'}A$ under $b_k$. Let $c$ be a point derivation of $\Gamma(A_k,U_e)$ at the $k$-point given by $e_1$ (a $k$-linear map $D$ with $D(ab)=\mathrm{ev}(a)D(b)+\mathrm{ev}(b)D(a)$) with values in $\mathrm{Hom}_k(V^\vee,\check C^1((\mathcal W.\mathrm{comap}\,b_k),\mathcal O_{P_k}))$, and assume that for every strictly increasing pair $s=(s(0)<s(1))$ there are coordinates $c_s\colon\Gamma(A_k,U_e)\to\mathrm{Hom}_k(V^\vee,k\otimes_{T'}\Gamma(A\times_{T'}A,W_s))$ satisfying `IsTangentCoordsOfPairAt` for the pair of morphisms $\operatorname{Spec}\Gamma(A\times_{T'}A,W_s)\to A$ obtained from the affine chart of $W_s$ by restricting $m_{s(0)}$ and $m_{s(1)}$ — that is, there are a thickening-valued point $w_0$ of $A_k$ over the base whose composite into $A$ is a tangent of that pair in the sense of `IsTangentOfPair`, and a factorisation $w_1$ through $U_e$ of the $L_k$-translate of $w_0$, with $c_s$ the tangent coordinates of the chart homomorphism of $w_1$ — and such that $\sigma_s(c_s(a)(\xi))=c(a)(\xi)_s$ for all $a,\xi$. Then for every $a\in\Gamma(A_k,U_e)$ and every $\xi\in V^\vee$ the $1$-cochain on the cover $(\mathcal W.\mathrm{comap}\,b_k).\mathrm{comap}\,i_X$ of $A_k$ whose component at $t$ is $i_X$ applied on sections to $c(a)(\xi)_t$, restricted to the intersection of the preimages, equals $d^0$ of some $0$-cochain with values in `OModulePresheaf.unit` of $f_k$; and the same holds with $i_Y$ in place of $i_X$.
--
--   This is the vanishing step for the obstruction to globalising local lifts of the multiplication of an abelian scheme along a small extension: the obstruction $1$-cocycle, restricted to the two unit slices $A_k\times e$ and $e\times A_k$, is a Čech coboundary, because along those slices the lifting problem has the global solution $\mathrm{id}_A$ provided by the lifted unit section $e$. It is used by [`GoodReductionJacobian.RelativeGroupLaw.exists_pointDerivations_obstruction_cocycle_of_local_lifts`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_pointDerivations_obstruction_cocycle_of_local_lifts).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_d_comap_slice_eq_of_obstruction_cocycle.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_d_comap_slice_eq_of_obstruction_cocycle
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
