-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_pointDerivations_d_eq_obstruction_two_cocycle
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_pointDerivations_d_eq_obstruction_two_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/df1e45cf-9a3b-5a32-8914-c2351cb0262a
-- title:
--   Abelian schemes: obstruction 2-cocycle is a coboundary
-- statement:
--   The setting is a small extension of Artinian local base rings. Let $T'$ be a commutative local Artinian ring whose residue field $k = \mathrm{ResidueField}\,T'$ is algebraically closed, let $T$ be a commutative ring, and let $\pi : T' \to T$ be a ring homomorphism which is surjective (`hπ`), has nilpotent kernel (`hker`), and is small in the sense that $(\ker \pi)\cdot \mathfrak m_{T'} = 0$ (`hsmall`); in addition $\ker\pi \le \mathfrak m_{T'}$ (`hI`). Let $\rho : T \to k$ be a ring homomorphism with $\rho \circ \pi$ the residue map of $T'$ (`hρ`).
--
--   Over $\mathrm{Spec}\,T$ there is a scheme $A_0$ with a separated smooth structure morphism $f_0 : A_0 \to \mathrm{Spec}\,T$, carrying a relative group law $L_0$ (functorial multiplication, unit and inverse on the sets $\{\varphi : S \to A_0 \mid \varphi \circ f_0 = t\}$ of $T$-scheme morphisms over each $t : S \to \mathrm{Spec}\,T$, subject to associativity, the unit laws, left inverses and compatibility with base change along $S' \to S$), assumed commutative (`hc₀`), and satisfying the predicate `AbelianSchemePropertyBundle T f₀` (`h₀`), i.e. $f_0$ is smooth and proper with connected fibres and admits a relative group law. The hypothesis `hH1` provides a numerical witness: an algebraically closed field $k'$, a scheme $A_{k'}$ with structure morphism $f_{k'}$ to $\mathrm{Spec}\,k'$, a morphism $A_{k'} \to A_0$ and a ring homomorphism $T \to k'$ forming a cartesian square, a natural number $g$ with $f_{k'}$ smooth of relative dimension $g$, and an ordered affine cover $\mathcal K$ of $A_{k'}$ such that $g$ is at most the $k'$-dimension of the first Čech cohomology of the structure sheaf computed from $\mathcal K$, i.e. `(OModulePresheaf.unit fk').cechFinrank 𝒦 1`.
--
--   The kernel of $\pi$ is presented linearly: $V$ is a $k$-vector space of finite dimension, also a $T'$-module compatibly (with the left and right $k$-actions agreeing), and $\iota : V \to T'$ is an injective $T'$-linear map (`hι`) whose range is $\ker\pi$ viewed as a $T'$-submodule of $T'$ (`hιI`).
--
--   The local lifting data consist of a finite ordered affine cover $\mathcal U = (U_a)_{a \in \mathcal U.\iota}$ of $A_0$ by affine opens indexed by a linearly ordered finite type, schemes $Y_a$ with smooth structure morphisms $q_a : Y_a \to \mathrm{Spec}\,T'$ (`hq`), and morphisms $g_a : U_a \to Y_a$ such that each square formed by $g_a$, the composite $U_a \hookrightarrow A_0 \to \mathrm{Spec}\,T$, $q_a$ and $\mathrm{Spec}\,\pi$ is cartesian (`hg`); thus $Y_a$ is a smooth lift of $U_a$ over $T'$.
--
--   The special fibre is given by a scheme $A_k$ with separated structure morphism $f_k : A_k \to \mathrm{Spec}\,k$, a relative group law $L_k$ on $f_k$, and an affine morphism $i_0 : A_k \to A_0$ making the square with $f_k$, $f_0$ and $\mathrm{Spec}\,\rho$ cartesian (`hi₀`); $L_k$ is commutative (`hck`), $f_k$ satisfies `AbelianSchemePropertyBundle k fk` (`hAk`), and `hLk` says that $i_0$ is a homomorphism: for every $t : S \to \mathrm{Spec}\,k$ and every pair $P, Q$ of morphisms $S \to A_k$ over $t$, the composite of $L_k.\mathrm{mul}\,t\,P\,Q$ with $i_0$ equals the product under $L_0$, over $t$ followed by $\mathrm{Spec}\,\rho$, of $P \circ i_0$ and $Q \circ i_0$. Moreover $U_e \subseteq A_k$ is an affine open (`hUe`) containing the identity, in the form of a morphism $e_1 : \mathrm{Spec}\,k \to U_e$ whose composite with the inclusion is the identity section $L_k.\mathrm{one}(\mathrm{id})$ (`he₁`).
--
--   The lifts of the opens of $A_0$ are organised by a family $O_a : A_0.\mathrm{Opens} \to (Y_a).\mathrm{Opens}$ with: $g_a^{-1}(O_a W) = (U_a \hookrightarrow A_0)^{-1} W$ (`hO`), monotonicity (`hOm`), $O_a(U_a) = \top$ (`hOtop`), $O_a W \cap O_a W' \le O_a(W \cap W')$ (`hOinf`), and affineness of $O_a W$ for affine $W \le U_a$ (`hOaff`).
--
--   The Čech identifications are the data $\sigma$: for every $n$ and every strictly increasing $(n+1)$-tuple $s$ of indices, a ring isomorphism $\sigma_s$ from $k \otimes_{T'} \Gamma(Y_{s_0}, O_{s_0}(\bigcap_j U_{s_j}))$ onto $\Gamma(A_k, \bigcap_j i_0^{-1} U_{s_j})$, where the target uses the cover `𝒰.comap i₀` of $A_k$ obtained by pulling $\mathcal U$ back along $i_0$. These are pinned geometrically by `hσ₁`, which states that the isomorphism onto the spectrum of the intersection, followed by $\mathrm{Spec}$ of $\sigma_s$, then $\mathrm{Spec}$ of the inclusion of the right tensor factor, then the canonical morphism from the spectrum of $\Gamma(Y_{s_0}, O_{s_0}(\bigcap_j U_{s_j}))$, coincides with the morphism induced by $i_0$ on that intersection followed by the inclusion into $U_{s_0}$ and by $g_{s_0}$; and by `hσ₂`, which states that $\sigma_s(x \otimes 1)$ is the image of $x \in k$ under the structural algebra map.
--
--   The transition data are isomorphisms $\varphi_{ab} : O_a(U_a \cap U_b) \cong O_b(U_a \cap U_b)$ for $a < b$, compatible with the structure morphisms to $\mathrm{Spec}\,T'$ (`hφq`), reducing to the identity in the sense that there are morphisms $\gamma, \gamma'$ from $U_a \cap U_b$ into the two opens which are induced by $g_a$, respectively $g_b$, and satisfy $\gamma$ followed by $\varphi_{ab}$ equal to $\gamma'$ (`hφg`), and compatible with the families $O_a$, $O_b$ on preimages of opens (`hφO`). For every strictly increasing triple $r = (r_0 < r_1 < r_2)$ there are further isomorphisms $\rho_{ab}(r)$, $\rho_{bc}(r)$, $\rho_{ac}(r)$ between the corresponding opens $O_{r_i}(U_{r_0} \cap U_{r_1} \cap U_{r_2})$, each compatible with the relevant $\varphi$ through the inclusion morphisms of opens (`hρab`, `hρbc`, `hρac`).
--
--   Finally, $\omega$ is an element of [`Algebra.PointDerivations k Γ(Ak, Ue) ev M`](def/Algebra_PointDerivations.html#L9), the $k$-submodule of $k$-linear maps $D : \Gamma(A_k, U_e) \to M$ satisfying $D(ab) = \mathrm{ev}(a)\,D(b) + \mathrm{ev}(b)\,D(a)$, where $\mathrm{ev}$ is the evaluation ring homomorphism at the identity section determined by $e_1$ and $M$ is the space of $k$-linear maps from the dual $V^{*}$ to the Čech $2$-cochains of the unit $\mathcal O$-module presheaf of $f_k$ on the cover $i_0^{-1}\mathcal U$. The hypothesis `hω` identifies $\omega$ as the obstruction: for every strictly increasing triple $r$ there is a map $cs$ from $\Gamma(A_k, U_e)$ to $k$-linear maps $V^{*} \to k \otimes_{T'} \Gamma(Y_{r_0}, O_{r_0}(\bigcap_j U_{r_j}))$ which is a system of tangent coordinates, in the sense of the predicate `IsTangentCoordsOfPairAtVia`, for the pair of morphisms given by the inverse of the affine identification followed by $\rho_{ac}(r)$ and the inclusion, respectively followed by $\rho_{ab}(r)$, $\rho_{bc}(r)$ and the inclusion, taken relative to $f_k$, $L_k$, the open $i_0^{-1}U_{r_2}$ with the morphism induced by $i_0$ followed by $g_{r_2}$, and the chart $U_e$; unfolded, this asserts the existence of a morphism $w_0$ from the spectrum of the thickening $(k \otimes_{T'} C) \otimes_k (k \oplus V)$, $C = \Gamma(Y_{r_0}, O_{r_0}(\bigcap_j U_{r_j}))$, into that open, lying over the canonical base morphism, such that $w_0$ composed with the chart morphism exhibits the pair of morphisms as a tangent vector in the sense of `IsTangentOfPair` for $\ker\pi$, $V$, $\iota$, together with a morphism $w_1$ into $U_e$ which is the translate of $w_0$ to the identity by $L_k$, and with $cs$ equal to the tangent coordinates of the ring homomorphism attached to $w_1$. In addition `hω` requires $\sigma_r(cs\,a\,\xi) = \omega(a)(\xi)(r)$ for all $a \in \Gamma(A_k, U_e)$ and $\xi \in V^{*}$. The hypothesis `hωZ` states that $\omega$ takes values in cocycles: the degree-$2$ Čech differential of the unit presheaf on $i_0^{-1}\mathcal U$ annihilates $\omega(a)(\xi)$ for all $a$ and $\xi$.
--
--   The conclusion is that $\omega$ is a coboundary, derivation-wise: there exists $\eta$ in [`Algebra.PointDerivations k Γ(Ak, Ue) ev M'`](def/Algebra_PointDerivations.html#L9), with $M'$ the space of $k$-linear maps from $V^{*}$ to the Čech $1$-cochains of the unit $\mathcal O$-module presheaf of $f_k$ on the cover $i_0^{-1}\mathcal U$, such that for all $a \in \Gamma(A_k, U_e)$ and all $\xi \in V^{*}$ the degree-$1$ Čech differential of $\eta(a)(\xi)$ equals $\omega(a)(\xi)$.
--
--   This is the formal counterpart of Grothendieck's theorem that abelian schemes are unobstructed: the $H^2$-valued obstruction to lifting an abelian scheme along a small surjection of Artinian local rings vanishes, here in the explicit Čech form where the obstruction class is packaged as a point derivation at the identity with values in $2$-cochains of the structure sheaf. It is the vanishing step used by [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_smooth_isPullback_of_ker_mul_maximalIdeal_eq_bot_of_le_cechFinrank`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_smooth_isPullback_of_ker_mul_maximalIdeal_eq_bot_of_le_cechFinrank), which produces the smooth lift of the abelian scheme over $T'$ by gluing the local lifts $Y_a$ after correcting the transition isomorphisms by the $1$-cochain $\eta$ furnished above.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_pointDerivations_d_eq_obstruction_two_cocycle.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct
  AlgebraicGeometry.SmallExtension Scheme.TwoAffineOpenCover

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_pointDerivations_d_eq_obstruction_two_cocycle
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀] [Smooth f₀]

    (L₀ : RelativeGroupLaw T f₀) (hc₀ : L₀.IsCommutative) (h₀ : AbelianSchemePropertyBundle T f₀)
    (hH1 : ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k)
      (Ak' : Scheme.{u}) (fk' : Ak' ⟶ Spec (CommRingCat.of k)) (i : Ak' ⟶ A₀) (ρ' : T →+* k)
      (_ : IsPullback i fk' f₀ (Spec.map (CommRingCat.ofHom ρ'))) (g : ℕ) (_ : SmoothOfRelativeDimension g fk')
      (𝒦 : Ak'.OrderedAffineCover), g ≤ (OModulePresheaf.unit fk').cechFinrank 𝒦 1)

    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) [IsSeparated fk]
    (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) [IsAffineHom i₀] (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))
    (hck : Lk.IsCommutative) (hAk : AbelianSchemePropertyBundle (ResidueField T') fk)
    (hLk : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of (ResidueField T'))) (P Q : SchemeHomOver t fk),
      (Lk.mul t P Q).1 ≫ i₀ =
        (L₀.mul (t ≫ Spec.map (CommRingCat.ofHom ρ))
          ⟨P.1 ≫ i₀, by rw [Category.assoc, hi₀.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ i₀, by rw [Category.assoc, hi₀.w, ← Category.assoc, Q.2]⟩).1)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

    (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOtop : ∀ a, O a (𝒰.U a) = ⊤)
    (hOinf : ∀ (a : 𝒰.ι) (W W' : A₀.Opens), O a W ⊓ O a W' ≤ O a (W ⊓ W'))
    (hOaff : ∀ (a : 𝒰.ι) (W : A₀.Opens), IsAffineOpen W → W ≤ 𝒰.U a → IsAffineOpen (O a W))

    (σ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      ((ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))) ≃+* Γ(Ak, (𝒰.comap i₀).inter s))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) s).isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (σ s).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)) →ₐ[T']
              (ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))).toRingHom) ≫
          (hOaff (s.1 0) (𝒰.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 s) (𝒰.inter_le s 0)).fromSpec =
        Ak.homOfLE (𝒰.comap_inter_le i₀ s) ≫ (i₀ ∣_ 𝒰.inter s) ≫ A₀.homOfLE (𝒰.inter_le s 0) ≫ g (s.1 0))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒰.Idx n) (x : ResidueField T'),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      letI := algebraOfHom fk ((𝒰.comap i₀).inter s)
      σ s (x ⊗ₜ[T'] (1 : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)))) = algebraMap (ResidueField T') Γ(Ak, (𝒰.comap i₀).inter s) x)

    (φ : ∀ (a b : 𝒰.ι), a < b → ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))))
    (hφq : ∀ (a b : 𝒰.ι) (h : a < b),
      (φ a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a)
    (hφg : ∀ (a b : 𝒰.ι) (h : a < b),
      ∃ (γ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
        (γ' : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
        γ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a ∧
        γ' ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b ∧
        γ ≫ (φ a b h).hom = γ')
    (hφO : ∀ (a b : 𝒰.ι) (h : a < b) (W : A₀.Opens),
      (φ a b h).hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W)

    (ρab : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 1) (𝒰.inter r))))
    (ρbc : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 1) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (ρac : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (hρab : ∀ r : 𝒰.Idx 2,
      (ρab r).hom ≫ (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) ≫
          (φ (r.1 0) (r.1 1) (r.2 (by decide))).hom)
    (hρbc : ∀ r : 𝒰.Idx 2,
      (ρbc r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) =
        (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) ≫
          (φ (r.1 1) (r.1 2) (r.2 (by decide))).hom)
    (hρac : ∀ r : 𝒰.Idx 2,
      (ρac r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) ≫
          (φ (r.1 0) (r.1 2) (r.2 (by decide))).hom)

    (ω : letI := algebraOfHom fk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fk).cochain (𝒰.comap i₀) 2)))
    (hω : ∀ r : 𝒰.Idx 2,
      letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
      letI := algebraOfHom fk Ue
      ∃ cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                ((ResidueField T') ⊗[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))),
        IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρab r).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          fk Lk (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) Ue cs ∧
        ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ r (cs a ξ) = ω.1 a ξ r)
    (hωZ : letI := algebraOfHom fk Ue
      ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit fk).d (𝒰.comap i₀) 2 (ω.1 a ξ) = 0)
    :
    letI := algebraOfHom fk Ue
    ∃ η : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fk).cochain (𝒰.comap i₀) 1)),
      ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit fk).d (𝒰.comap i₀) 1 (η.1 a ξ) = ω.1 a ξ := by sorry
