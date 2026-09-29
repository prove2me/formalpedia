-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_mul_lift_of_pointDerivations_coboundary
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_pointDerivations_coboundary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/7f6e53a6-9b92-5dfa-ab0d-e43cbafc0734
-- title:
--   A coboundary of the obstruction cocycle lifts the multiplication
-- statement:
--   Let $T'$ be an Artinian local ring with algebraically closed residue field $k=\mathrm{ResidueField}\,T'$, let $T$ be a commutative ring, and let $\pi : T' \to T$ be a surjective ring homomorphism whose kernel is nilpotent, contained in the maximal ideal and annihilated by it, $\ker\pi\cdot\mathfrak m_{T'}=0$; let $\rho : T \to k$ satisfy $\rho\circ\pi =$ the residue map. Let $f_0 : A_0 \to \operatorname{Spec} T$ carry a commutative relative group law $L_0$ and satisfy `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, admitting a relative group law); let $f : A \to \operatorname{Spec} T'$ be smooth and proper, $g : A_0 \to A$ a morphism making $A_0$ the base change of $A$ along $\operatorname{Spec}\pi$, and $e$ a section of $f$ over $\operatorname{Spec} T'$ whose reduction is the unit of $L_0$ followed by $g$. Let $V$ be a finite-dimensional $k$-vector space, also a $T'$-module compatibly, with an injective $T'$-linear $\iota : V \to T'$ whose image is $\ker\pi$. Write $P = A\times_{T'}A$, assumed separated over $T'$, and let $\mathcal W$ be an ordered affine cover of $P$ (a finite linearly ordered family of affine opens covering $P$) equipped with morphisms $m_i : \mathcal W.U_i \to A$ over $T'$ which, restricted to the special fibre, agree with the multiplication $L_0.\mathrm{mul}$ of the two projections of $A_0\times_T A_0$ followed by $g$. On the special fibre let $f_k : A_k \to \operatorname{Spec} k$ carry a relative group law $L_k$, with $i_0 : A_k \to A_0$ exhibiting $A_k$ as the base change along $\operatorname{Spec}\rho$, an affine open $U_e \subseteq A_k$ and a section $e_1 : \operatorname{Spec} k \to U_e$ whose composite with the inclusion is the unit of $L_k$; let $b_k : P_k \to P$ be an affine morphism exhibiting $P_k$ as the fibre of $P$ over $k$, together with ring isomorphisms $\sigma_s : k\otimes_{T'}\Gamma(P,\mathcal W_s) \cong \Gamma(P_k,(b_k^{-1}\mathcal W)_s)$ for every strictly increasing tuple $s$, compatible with $1\otimes x \mapsto$ restriction of $b_k^\ast x$ and with the structure maps of $k$, and let $p_1,p_2 : P_k \to A_k$ over $k$ present $P_k$ as $A_k\times_k A_k$ and be compatible with the two projections of $P$ through $i_0 \circ g$. Let $c$ be a point derivation of $\Gamma(A_k,U_e)$ over $k$ at the evaluation homomorphism given by $e_1$, valued in $\mathrm{Hom}_k(V^\vee, \check C^1)$, where $\check C^n$ denotes the degree-$n$ Čech cochains of the presheaf `OModulePresheaf.unit` of $p_1 \ggg f_k$ for the cover $b_k^{-1}\mathcal W$, and assume that for every pair $s=(i<j)$ there is a family $c_s$ with values in $\mathrm{Hom}_k(V^\vee, k\otimes_{T'}\Gamma(P,\mathcal W_s))$ satisfying `IsTangentCoordsOfPairAt` for $\ker\pi$, $V$, $\iota$, the ring $\Gamma(P,\mathcal W_s)$, the two morphisms $\operatorname{Spec}\Gamma(P,\mathcal W_s) \to A$ obtained from the canonical isomorphism of the affine open $\mathcal W_s$ followed by the inclusions into $\mathcal W.U_i$, $\mathcal W.U_j$ and the maps $m_i$, $m_j$, the data $f_k$, $L_k$, $i_0 \ggg g$ and $U_e$ — that is, there are a point $w_0$ of $A_k$ with values in the thickening $(k\otimes_{T'}\Gamma(P,\mathcal W_s))\otimes_k (k\oplus V)$ over the base and a lift $w_1$ into $U_e$ such that $w_0$ followed by $i_0 \ggg g$ is a tangent of the pair in the sense of `IsTangentOfPair`, $w_1$ followed by the inclusion of $U_e$ is the $L_k$-translate of $w_0$ to the unit, and $c_s$ is the tangent-coordinate function of the chart homomorphism of $w_1$ — and such that $\sigma_s(c_s(a)(\xi)) = c(a)(\xi)_s$ for all $a \in \Gamma(A_k,U_e)$ and $\xi \in V^\vee$. Finally assume $c$ is a Čech coboundary: there is a point derivation $b$ at the same point valued in $\mathrm{Hom}_k(V^\vee,\check C^0)$ with $d^0(b(a)(\xi)) = c(a)(\xi)$ for all $a$ and $\xi$. Then there exists a morphism $m' : P \to A$ over $T'$ whose composite with the canonical morphism $A_0\times_T A_0 \to P$ induced by $g$ on both factors equals $L_0.\mathrm{mul}$ of the two projections of $A_0\times_T A_0$ followed by $g$.
--
--   This is the regluing step in the deformation-theoretic construction of a group law on a smooth proper lift of an abelian scheme across a small extension of Artinian local rings: once the Čech $1$-cocycle measuring the failure of the local lifts $m_i$ of the multiplication to agree on overlaps is trivialised by a $0$-cochain $b$, the twisted local lifts glue to a global multiplication $m' : A\times_{T'}A \to A$ reducing to the given one. It is used by [`GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_isPullback_of_ker_mul_maximalIdeal_eq_bot`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_isPullback_of_ker_mul_maximalIdeal_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_mul_lift_of_pointDerivations_coboundary.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_pointDerivations_coboundary
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
