-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_obstruction_two_cocycle
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_unitPullback_mul_sub_fst_sub_snd_obstruction_two_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/e85364ec-9503-540f-a7fb-ef9f100b2fd5
-- title:
--   Primitivity of the obstruction cocycle of an abelian scheme
-- statement:
--   Throughout, $k$ denotes the residue field `ResidueField T'` and $I=\ker\pi$.
--
--   **Small extension data.** $T'$ is a commutative Artinian local ring, $T$ a commutative ring, and $\pi : T' \to T$ a ring homomorphism which is surjective (`hπ`), whose kernel is nilpotent (`hker`), satisfies $I\cdot\mathfrak m_{T'}=0$ (`hsmall`) and $I \le \mathfrak m_{T'}$ (`hI`). A ring homomorphism $\rho : T \to k$ is given with $\rho\circ\pi$ the residue map (`hρ`). The ideal $I$ is coordinatised by a $k$-vector space $V$ of finite dimension, carrying compatible $T'$-module and right $k$-module structures, together with a $T'$-linear map $\iota : V \to T'$ which is injective (`hι`) and whose range is $I$ regarded as a $T'$-submodule (`hιI`).
--
--   **The scheme over $T$ and its special fibre.** $f_0 : A_0 \to \operatorname{Spec} T$ is separated and smooth, equipped with a relative group law $L_0$ (functorial multiplication, unit and inverse on $T$-points with associativity, unit and inverse laws and naturality) and with the bundle `AbelianSchemePropertyBundle T f₀` (`h₀`: $f_0$ smooth and proper, all its fibres $f_0^{-1}(s)$ connected, and a relative group law exists). Further, $f_k : A_k \to \operatorname{Spec} k$ is separated with a relative group law $L_k$, and $i_0 : A_k \to A_0$ is an affine morphism making the square with $f_k$, $f_0$ and $\operatorname{Spec}\rho$ a pullback (`hi₀`). The law $L_k$ is commutative (`hck`), $f_k$ satisfies `AbelianSchemePropertyBundle (ResidueField T') fk` (`hAk`), and $i_0$ is a homomorphism: for all $t : S \to \operatorname{Spec} k$ and all $P,Q$ over $t$, $(L_k.\mathrm{mul}\,t\,P\,Q)$ followed by $i_0$ is the $L_0$-product of $P$ followed by $i_0$ and $Q$ followed by $i_0$ over $t$ followed by $\operatorname{Spec}\rho$ (`hLk`). Finally $U_e$ is an affine open of $A_k$ (`hUe`) with a morphism $e_1 : \operatorname{Spec} k \to U_e$ whose composite with the open immersion is the unit section of $L_k$ (`he₁`).
--
--   **Cover and local lifts.** $\mathcal U$ is an ordered affine cover of $A_0$ (a finite linearly ordered family of affine opens with supremum $\top$). For each index $a$ there are a scheme $Y_a$, a smooth morphism $q_a : Y_a \to \operatorname{Spec} T'$ (`hq`) and a morphism $g_a : U_a \to Y_a$ such that $g_a$, the composite of the immersion $U_a \hookrightarrow A_0$ with $f_0$, $q_a$ and $\operatorname{Spec}\pi$ form a pullback square (`hg`); thus $U_a$ is the reduction of the smooth lift $Y_a$ over $T'$.
--
--   **The system of opens.** For each $a$ there is an order-preserving assignment $W \mapsto O_a(W)$ from opens of $A_0$ to opens of $Y_a$ (`hOm`) with $g_a^{-1}O_a(W) = W \cap U_a$ (more precisely the preimage of $W$ under $U_a \hookrightarrow A_0$, `hO`), $O_a(U_a)=\top$ (`hOtop`), $O_a(W)\cap O_a(W') \le O_a(W\cap W')$ (`hOinf`), and $O_a(W)$ affine whenever $W$ is affine and contained in $U_a$ (`hOaff`).
--
--   **Chart identifications.** For every $n$ and every strictly increasing tuple $s=(s_0<\dots<s_n)$ of indices, writing $\mathcal U.\mathrm{inter}\,s=\bigcap_j U_{s_j}$, a ring isomorphism
--   $$\sigma_s : k \otimes_{T'} \Gamma\bigl(Y_{s_0}, O_{s_0}(\textstyle\bigcap_j U_{s_j})\bigr) \;\xrightarrow{\ \sim\ }\; \Gamma\bigl(A_k, \textstyle\bigcap_j i_0^{-1}U_{s_j}\bigr)$$
--   is given, the source being formed for the $T'$-algebra structure coming from $q_{s_0}$. Two compatibilities are imposed: `hσ₁` says that the canonical isomorphism of the affine open $\bigcap_j i_0^{-1}U_{s_j}$ with its spectrum, followed by $\operatorname{Spec}\sigma_s$, by $\operatorname{Spec}$ of the inclusion $c \mapsto 1\otimes c$, and by the canonical morphism from the spectrum of $\Gamma(Y_{s_0},O_{s_0}(\bigcap_j U_{s_j}))$ to that open, agrees with the restriction of $i_0$ to $\bigcap_j i_0^{-1}U_{s_j} \to \bigcap_j U_{s_j}$ followed by the inclusion into $U_{s_0}$ and by $g_{s_0}$; `hσ₂` says that $\sigma_s(x\otimes 1)$ is the image of $x \in k$ under the structure map of $\Gamma(A_k,\bigcap_j i_0^{-1}U_{s_j})$ as a $k$-algebra via $f_k$.
--
--   **Transition isomorphisms.** For $a<b$ an isomorphism $\varphi_{ab} : O_a(U_a\cap U_b) \cong O_b(U_a\cap U_b)$ is given, compatible with the structure morphisms to $\operatorname{Spec} T'$ (`hφq`), with the lifts in the sense that there are morphisms $\gamma, \gamma'$ from $U_a \cap U_b$ to $O_a(U_a\cap U_b)$, $O_b(U_a\cap U_b)$ lifting $g_a$, $g_b$ and satisfying $\gamma$ followed by $\varphi_{ab}$ equal to $\gamma'$ (`hφg`), and with the system $O$ in the sense that $\varphi_{ab}$ pulls the trace of $O_b(W)$ back to the trace of $O_a(W)$ for every open $W$ of $A_0$ (`hφO`). For each strictly increasing triple $r=(r_0<r_1<r_2)$ three isomorphisms $\rho_{ab}(r), \rho_{bc}(r), \rho_{ac}(r)$ between the opens $O_{r_0}$, $O_{r_1}$, $O_{r_2}$ of $\bigcap_j U_{r_j}$ are given, each compatible with the corresponding $\varphi$ through the inclusions of opens (`hρab`, `hρbc`, `hρac`).
--
--   **The obstruction cochain.** $\omega$ is an element of the $k$-module of point derivations [`Algebra.PointDerivations`](def/Algebra_PointDerivations.html#L9) of the $k$-algebra $\Gamma(A_k,U_e)$ (its algebra structure coming from $f_k$) at the evaluation homomorphism $\Gamma(A_k,U_e) \to k$ determined by the unit section $e_1$, with values in $\operatorname{Hom}_k\bigl(V^\vee, \check C^2(i_0^{-1}\mathcal U)\bigr)$; here $V^\vee =$ `Module.Dual k V`, $\check C^2$ denotes the degree $2$ cochains of the presheaf `OModulePresheaf.unit fk` for the cover $i_0^{-1}\mathcal U$ obtained from $\mathcal U$ by `comap` along $i_0$, and a point derivation is a $k$-linear $D$ with $D(ab)=\mathrm{ev}(a)\,D(b)+\mathrm{ev}(b)\,D(a)$.
--
--   Two properties of $\omega$ are assumed. The hypothesis `hω` requires, for each strictly increasing triple $r$, a family $\mathrm{cs} : \Gamma(A_k,U_e) \to \operatorname{Hom}_k\bigl(V^\vee, k\otimes_{T'}\Gamma(Y_{r_0},O_{r_0}(\bigcap_j U_{r_j}))\bigr)$ with two properties. First, `IsTangentCoordsOfPairAtVia` holds for $I$, $V$, $\iota$, the ring $C = \Gamma(Y_{r_0},O_{r_0}(\bigcap_j U_{r_j}))$, the two morphisms $u,v : \operatorname{Spec} C \to Y_{r_2}$ given by the inverse of the canonical isomorphism of the affine open $O_{r_0}(\bigcap_j U_{r_j})$ with its spectrum followed by $\rho_{ac}(r)$, respectively by $\rho_{ab}(r)$ and then $\rho_{bc}(r)$, and then by the open immersion of $O_{r_2}(\bigcap_j U_{r_j})$, for the data $f_k$, $L_k$, the open $i_0^{-1}U_{r_2}$ with the morphism obtained by restricting $i_0$ to $i_0^{-1}U_{r_2} \to U_{r_2}$ and composing with $g_{r_2}$, the chart $U_e$, and $\mathrm{cs}$; that is, there are a morphism $w_0$ from the spectrum of the thickening $(k\otimes_{T'}C)\otimes_k (k \oplus V)$ (trivial square-zero extension) to $i_0^{-1}U_{r_2}$ lying over the relevant base morphism, and a morphism $w_1$ from that spectrum to $U_e$, such that $w_0$ followed by the above morphism is a tangent of the pair $(u,v)$ in the sense of `IsTangentOfPair` (it factors, through a Schlessinger map out of the pair ring of $I$ over $C$, a morphism whose two specialisations along the two projections of the pair ring are $u$ and $v$), $w_1$ followed by the open immersion of $U_e$ is the translate of $w_0$ by $L_k$ to the unit section, and $\mathrm{cs}$ is the tangent-coordinate function of the ring homomorphism $\Gamma(A_k,U_e) \to$ thickening attached to $w_1$. Second, $\sigma_r(\mathrm{cs}(a)(\xi)) = \omega(a)(\xi)(r)$ for all $a \in \Gamma(A_k,U_e)$ and $\xi \in V^\vee$. The hypothesis `hωZ` requires that $\omega(a)(\xi)$ be a cocycle: its Čech differential in degree $2$ for the cover $i_0^{-1}\mathcal U$ vanishes for all $a$ and $\xi$.
--
--   **Cover of the square.** $\mathcal W$ is an ordered affine cover of $A_k \times_k A_k$ (the pullback of $f_k$ with itself), and $\lambda_1,\lambda_2,\lambda_3 : \mathcal W.\iota \to \mathcal U.\iota$ are index maps refining $i_0^{-1}\mathcal U$ along the first projection $p_1$ (`h₁`), the second projection $p_2$ (`h₂`) and the multiplication $\mu_k = \bigl(L_k.\mathrm{mul}\,(p_1\circ f_k\text{-base})\,\langle p_1\rangle\,\langle p_2\rangle\bigr)$ (`h₃`): for every $w$, $\mathcal W_w$ is contained in the preimage under the respective morphism of $i_0^{-1}U_{\lambda_i(w)}$.
--
--   **Conclusion.** For every $a \in \Gamma(A_k,U_e)$ and every $\xi \in V^\vee$ there exists a $1$-cochain $b$ of the presheaf `OModulePresheaf.unit` for $A_k\times_k A_k$ over $k$ (taken via $p_1$ followed by $f_k$) relative to the cover $\mathcal W$, that is, a family of sections of the structure sheaf over the pairwise intersections of $\mathcal W$, whose Čech differential satisfies
--   $$d^1 b \;=\; \mu_k^{*}\bigl(\omega(a)(\xi)\bigr) \;-\; p_1^{*}\bigl(\omega(a)(\xi)\bigr) \;-\; p_2^{*}\bigl(\omega(a)(\xi)\bigr),$$
--   where each pull-back is the degree $2$ cochain pull-back `OModulePresheaf.unitPullback` from the cover $i_0^{-1}\mathcal U$ of $A_k$ to the cover $\mathcal W$ along the indicated morphism, taken with the index map $\lambda_3$, $\lambda_1$, $\lambda_2$ and the corresponding refinement witness $h_3$, $h_1$, $h_2$; by definition this pull-back acts index-wise by pulling back sections along the morphism and restricting, inserting the sign of the permutation that sorts the image index tuple, and giving $0$ on tuples whose image is not injective.
--
--   This is the cochain-level primitivity of the obstruction to lifting an abelian scheme along a small extension: pulled back to $A_k \times_k A_k$ along the group law, the obstruction $2$-cocycle differs from the sum of its pull-backs along the two projections by a Čech coboundary, which is the functoriality of obstruction classes in the group-scheme setting. It is the input used by [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_pointDerivations_d_eq_obstruction_two_cocycle`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_pointDerivations_d_eq_obstruction_two_cocycle), where primitivity is combined with a vanishing argument to produce a lift of the abelian scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_obstruction_two_cocycle.lean

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
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct
  AlgebraicGeometry.SmallExtension Scheme.TwoAffineOpenCover

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_unitPullback_mul_sub_fst_sub_snd_obstruction_two_cocycle
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀] [Smooth f₀]

    (L₀ : RelativeGroupLaw T f₀) (h₀ : AbelianSchemePropertyBundle T f₀)

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

    (𝒲 : (pullback fk fk).OrderedAffineCover) (lam₁ lam₂ lam₃ : 𝒲.ι → 𝒰.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ pullback.fst fk fk ⁻¹ᵁ (𝒰.comap i₀).U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ pullback.snd fk fk ⁻¹ᵁ (𝒰.comap i₀).U (lam₂ w))
    (h₃ : ∀ w, 𝒲.U w ≤
      (Lk.mul (pullback.fst fk fk ≫ fk) ⟨pullback.fst fk fk, rfl⟩ ⟨pullback.snd fk fk, pullback.condition.symm⟩).1 ⁻¹ᵁ
        (𝒰.comap i₀).U (lam₃ w)) :
    letI := algebraOfHom fk Ue
    ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
      ∃ b : (OModulePresheaf.unit (pullback.fst fk fk ≫ fk)).cochain 𝒲 1,
        (OModulePresheaf.unit (pullback.fst fk fk ≫ fk)).d 𝒲 1 b =
          OModulePresheaf.unitPullback (πX := pullback.fst fk fk ≫ fk)
              (Lk.mul (pullback.fst fk fk ≫ fk) ⟨pullback.fst fk fk, rfl⟩ ⟨pullback.snd fk fk, pullback.condition.symm⟩).1
              𝒲 (𝒰.comap i₀) lam₃ h₃ 2 (ω.1 a ξ) -
            OModulePresheaf.unitPullback (πX := pullback.fst fk fk ≫ fk) (pullback.fst fk fk)
              𝒲 (𝒰.comap i₀) lam₁ h₁ 2 (ω.1 a ξ) -
            OModulePresheaf.unitPullback (πX := pullback.fst fk fk ≫ fk) (pullback.snd fk fk)
              𝒲 (𝒰.comap i₀) lam₂ h₂ 2 (ω.1 a ξ) := by sorry
