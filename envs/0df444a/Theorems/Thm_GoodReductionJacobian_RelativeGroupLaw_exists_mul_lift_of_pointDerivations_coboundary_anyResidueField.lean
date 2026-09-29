-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_mul_lift_of_pointDerivations_coboundary_anyResidueField
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_pointDerivations_coboundary_anyResidueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/d242f20b-0e89-537a-acef-daa8a90555fd
-- title:
--   Coboundary of the tangent cochain lifts the group law
-- statement:
--   Let $T'$ be an Artinian local ring with maximal ideal $\mathfrak m$ and residue field $k$, let $T$ be a commutative ring and $\pi\colon T'\to T$ a surjective ring homomorphism whose kernel $I=\ker\pi$ is nilpotent and satisfies $I\cdot\mathfrak m=\bot$ and $I\le\mathfrak m$, and let $\rho\colon T\to k$ satisfy $\rho\circ\pi=\mathrm{residue}$. Let $f_0\colon A_0\to\operatorname{Spec}T$ carry a relative group law $L_0$ (a functorial group structure on sections over $T$-schemes) which is commutative, and assume `AbelianSchemePropertyBundle` for $f_0$ ($f_0$ smooth and proper with connected fibres, admitting a relative group law). Let $f\colon A\to\operatorname{Spec}T'$ be smooth and proper, let $g\colon A_0\to A$ make $(g,f_0,f,\operatorname{Spec}\pi)$ a pullback square, and let $e$ be a section of $f$ reducing along $\operatorname{Spec}\pi$ to the unit section of $L_0$ followed by $g$. Let $V$ be a finite-dimensional $k$-vector space, also a $T'$-module compatibly with central right $k$-action, and $\iota\colon V\to T'$ an injective $T'$-linear map whose range is $I$. Assume $P=A\times_{\operatorname{Spec}T'}A$ separated over $\operatorname{Spec}T'$, and let $\mathcal W$ be a finite ordered affine cover of $P$ with morphisms $m_i\colon \mathcal W.U_i\to A$ over $\operatorname{Spec}T'$ such that each $m_i$, restricted along the canonical map $A_0\times_TA_0\to P$, agrees with $L_0.\mathrm{mul}$ of the two projections followed by $g$. Let $f_k\colon A_k\to\operatorname{Spec}k$ with relative group law $L_k$ and $i_0\colon A_k\to A_0$ forming a pullback over $\operatorname{Spec}\rho$, let $U_e\subseteq A_k$ be an affine open through which the unit section of $L_k$ factors via $e_1$, and let $b_k\colon P_k\to P$ be an affine morphism with $y_k\colon P_k\to\operatorname{Spec}k$ forming a pullback of $P\to\operatorname{Spec}T'$ along the residue map, together with ring isomorphisms $\sigma_s\colon k\otimes_{T'}\Gamma(P,\mathcal W_s)\cong\Gamma(P_k,(b_k^{-1}\mathcal W)_s)$, for all strictly increasing index tuples $s$, which send $1\otimes x$ to the restriction of $b_k^\ast x$ and $a\otimes 1$ to the image of $a$ under the structure map. Let $p_1,p_2\colon P_k\to A_k$ satisfy $p_j\circ\!$-compatibilities with $b_k$ composed with the two projections of $P$ and with $f_k$, and exhibit $P_k$ as $A_k\times_kA_k$. Let $c$ be a point derivation of $\Gamma(A_k,U_e)$ over $k$ at the evaluation homomorphism given by $e_1$ — a $k$-linear $D$ with $D(ab)=\mathrm{ev}(a)D(b)+\mathrm{ev}(b)D(a)$ — with values in $\operatorname{Hom}_k(V^\vee,\check C^1)$, where $\check C^i$ denotes the $i$-cochains of the structure-sheaf $\mathcal O$-module presheaf of $p_1\circ f_k$ on the cover $b_k^{-1}\mathcal W$; assume that for each pair $s=(s_0<s_1)$ there is $c_s\colon\Gamma(A_k,U_e)\to\operatorname{Hom}_k(V^\vee,k\otimes_{T'}\Gamma(P,\mathcal W_s))$ which is a system of tangent coordinates at the unit, in the sense of `IsTangentCoordsOfPairAt` for $I$, $V$, $\iota$ and $C=\Gamma(P,\mathcal W_s)$, for the pair of morphisms $\operatorname{Spec}C\to A$ obtained from $m_{s_0}$ and $m_{s_1}$ on the overlap (so $c_s$ is the tangent-coordinate function attached to a thickening point whose $L_k$-translate to the unit factors through $U_e$), and such that $\sigma_s(c_s(a)(\xi))=c(a)(\xi)_s$ for all $a,\xi$. Finally let $b$ be a point derivation at the same evaluation with values in $\operatorname{Hom}_k(V^\vee,\check C^0)$ whose Čech differential $d^0$ satisfies $d^0(b(a)(\xi))=c(a)(\xi)$ for all $a$ and $\xi$. The conclusion is that there exists $m'\colon P\to A$ with $m'$ followed by $f$ equal to the structure morphism of $P$, and such that the canonical map $A_0\times_TA_0\to P$ followed by $m'$ equals $L_0.\mathrm{mul}$ of the two projections followed by $g$.
--
--   This is the gluing step in the deformation-theoretic construction of a group law on a smooth proper lift $A$ of an abelian scheme $A_0$ across a small extension $T'\to T$: the local lifts $m_i$ of the multiplication differ on overlaps by a tangent-valued $1$-cochain, and its vanishing in Čech cohomology — here witnessed by an explicit $0$-cochain $b$ — allows the $m_i$ to be corrected to a global $m'$. It is used by [`GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_smallExtension`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_smallExtension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_mul_lift_of_pointDerivations_coboundary_anyResidueField.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_pointDerivations_coboundary_anyResidueField
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
          ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ s (cs a ξ) = c.1 a ξ s))
    (b : letI := algebraOfHom fk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit (p₁ ≫ fk)).cochain (𝒲.comap bk) 0)))
    (hb : letI := algebraOfHom fk Ue
      ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit (p₁ ≫ fk)).d (𝒲.comap bk) 0 (b.1 a ξ) = c.1 a ξ) :
    ∃ m' : pullback f f ⟶ A, m' ≫ f = pullback.fst f f ≫ f ∧
      (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ≫ m' =
        (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g := by sorry
