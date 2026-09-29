-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_comp_eq_comp_iff_map_tmul_sub_eq_zero_of_isRegluingBy_of_hom_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_comp_eq_comp_iff_map_tmul_sub_eq_zero_of_isRegluingBy_of_hom_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/726d8cc0-9838-5768-a1e3-4f5e376bbc7b
-- title:
--   Endomorphism lifts to a regluing iff its Kodaira–Spencer obstruction vanishes
-- statement:
--   Throughout, $B$ is a local artinian ring whose residue field $\kappa :=$ `ResidueField B` is algebraically closed, $B_1$ is a $B$-algebra, $J := \ker(B \to B_1)$, and $X_\kappa :=$ `pullback D₀.f (specMap B (ResidueField B))` denotes the base change of the deformation $D_0$ introduced below along $\operatorname{Spec}\kappa \to \operatorname{Spec} B$, with structural morphism $\pi_\kappa :=$ `pullback.snd` and first projection `pullback.fst` $: X_\kappa \to D_0.A$.
--
--   **Small-extension data.** The structure map $B \to B_1$ is surjective (`hπ`), its kernel $J$ is nilpotent (`hker`), satisfies $J\cdot\mathfrak m_B = 0$ (`hsmall`) and $J \subseteq \mathfrak m_B$ (`hI`). Over $B_1$ there is a morphism $f_1 : A_1 \to \operatorname{Spec} B_1$ carrying a relative group law $L_1$ which is commutative (`hc₁`) and satisfies `AbelianSchemePropertyBundle B₁ f₁` (`h₁`), i.e. $f_1$ is smooth and proper, all its fibres are connected, and a relative group law exists. Further, $V$ is a finite-dimensional $\kappa$-vector space carrying a compatible $B$-module structure and a central $\kappa^{\mathrm{op}}$-action, and $\iota : V \to B$ is an injective $B$-linear map (`hι`) whose range is exactly $J$, viewed as a $B$-submodule (`hιI`).
--
--   **The base deformation and its charts.** $D_0$ is a bare deformation of $(f_1, L_1)$ to $B$, that is: a scheme $D_0.A$ with a separated morphism $D_0.f : D_0.A \to \operatorname{Spec} B$, a commutative relative group law $D_0.L$ on it, the property bundle `AbelianSchemePropertyBundle B D₀.f`, and a morphism $D_0.g : A_1 \to D_0.A$ making the square with $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ cartesian and compatible with the two group laws on points. $\mathcal U$ is an ordered affine cover of $D_0.A$ (a finite linearly ordered index type, affine opens with supremum $\top$), $i_0$ is an index, and $e_0 : \operatorname{Spec} B \to U_{i_0}$ is a section with $e_0$ followed by the inclusion $U_{i_0} \hookrightarrow D_0.A$ equal to the unit section of $D_0.L$ (`he₀`). Similarly $e_1 : \operatorname{Spec}\kappa \to (\mathcal U_\kappa).U\,i_0$ satisfies, after composition with the inclusion, the analogous identity for the unit of the base-changed law `RelativeGroupLaw.baseChange (specMap B κ) D₀.L` (`he₁`), where $\mathcal U_\kappa :=$ `𝒰.baseChange D₀.f (ResidueField B)` is the cover of $X_\kappa$ obtained by taking preimages of the $U_i$ under `pullback.fst`. For each index $s$ of `𝒰.Idx 1` (a strictly monotone pair of indices, with $\mathcal U.\mathrm{inter}\,s$ the corresponding intersection) a ring isomorphism
--   $$\sigma_s : \kappa \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s) \;\xrightarrow{\ \sim\ }\; \Gamma(X_\kappa, \mathcal U_\kappa.\mathrm{inter}\,s)$$
--   is given, sending $1 \otimes x$ to the restriction of the pullback of $x$ along `pullback.fst` (`hσ₁`) and $a \otimes 1$ to the image of $a$ under the $\kappa$-algebra structure map of $\Gamma(X_\kappa, \mathcal U_\kappa.\mathrm{inter}\,s)$ (`hσ₂`).
--
--   **The tangent class of the regluing.** Write $C^n$ for the degree-$n$ Čech cochains of `OModulePresheaf.unit π_κ` with respect to $\mathcal U_\kappa$, $d^n$ for its differentials, and $ev$ for the evaluation ring homomorphism $\Gamma(X_\kappa, (\mathcal U_\kappa).U\,i_0) \to \kappa$ determined by $e_1$ (the composite `topIso.inv`, $e_1$ on global sections, and `Scheme.ΓSpecIso`). The datum $c$ is an element of [`Algebra.PointDerivations κ Γ(X_κ, (𝒰_κ).U i₀) ev`](def/Algebra_PointDerivations.html#L9) with values in $\operatorname{Hom}_\kappa(V^\vee, C^1)$, i.e. a $\kappa$-linear map satisfying the Leibniz rule $c(ab) = ev(a)\,c(b) + ev(b)\,c(a)$; by `hc` each value $c(a)(\xi)$ is a $1$-cocycle, that is, lies in $\ker d^1$.
--
--   **The regluing.** For each $s$, $\tau_s$ is a self-isomorphism of the scheme $\mathcal U.\mathrm{inter}\,s$, and $D$ is a second bare deformation of $(f_1,L_1)$ to $B$ with `D₀.IsRegluingBy 𝒰 τ D`, which says: each $\tau_s$ is a morphism over $B$ ($\tau_s$ followed by the inclusion and $D_0.f$ equals the inclusion followed by $D_0.f$); each $\tau_s$ fixes the restriction of $D_0.g$ to $\mathcal U.\mathrm{inter}\,s$; and there are open immersions $\iota_i : U_i \to D.A$ over $D_0.f$, jointly surjective on points, compatible with $D_0.g$ restricted to each $U_i$, and such that on each overlap indexed by $s$ one has $\mathrm{homOfLE}$ followed by $\iota_{s(0)}$ equal to $\tau_s$ followed by $\mathrm{homOfLE}$ followed by $\iota_{s(1)}$. The hypothesis `hτ` identifies $c$ as the cocycle of tangent coordinates of this regluing: for each $s$ there exists
--   $$cs : \Gamma(X_\kappa, (\mathcal U_\kappa).U\,i_0) \to \operatorname{Hom}_\kappa\bigl(V^\vee, \kappa \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s)\bigr)$$
--   satisfying [`AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt J V ι Γ(D₀.A, 𝒰.inter s)`](def/AlgebraicGeometry_TangentCoordsOfPairAt.html#L31) for the pair of $\Gamma(D_0.A,\mathcal U.\mathrm{inter}\,s)$-points of $D_0.A$ given by `fromSpec` of the affine open $\mathcal U.\mathrm{inter}\,s$ and by `isoSpec.inv` followed by $\tau_s$ followed by the inclusion, taken relative to $\pi_\kappa$, the base-changed group law, `pullback.fst` and the chart $(\mathcal U_\kappa).U\,i_0$ — that is, there are a point of $\operatorname{Spec}$ of the `thickening` ring lying over the prescribed base, a lift of its translate to the unit into the chart, and the coordinates read off that chart reproduce $cs$ — and moreover $\sigma_s(cs(a)(\xi))$ equals the $s$-component of $c(a)(\xi)$ for all $a$ and all $\xi \in V^\vee$.
--
--   **Presentation of the tangent space and of point derivations.** The open $(\mathcal U_\kappa).U\,i_0$ is affine (`hU`). $W$ is a $\kappa$-vector space and $\tau_W$ assigns to each $w \in W$ a $\kappa[\varepsilon]$-point of $X_\kappa$ over `tangentBase κ (RingHom.id κ)`, injectively (`hWinj`), with image exactly the tangent vectors at the unit — a point $P$ lies in the range of $\tau_W$ if and only if `tangentZero` followed by $P$ is the unit section of the base-changed law at the corresponding geometric point (`hWrange`) — additively (`hWadd`: $\tau_W(v+w)$ is the product of $\tau_W(v)$ and $\tau_W(w)$ under the base-changed law) and $\kappa$-homogeneously (`hWsmul`: $\tau_W(a\cdot v)$ is `tangentScale κ a` followed by $\tau_W(v)$). The datum $\Phi$ gives, for every $\kappa$-vector space $M$, a $\kappa$-linear isomorphism from the module of point derivations of $\Gamma(X_\kappa, (\mathcal U_\kappa).U\,i_0)$ at $ev$ with values in $M$ onto $W \otimes_\kappa M$; it is natural in $M$, i.e. compatible with [`Algebra.PointDerivations.map`](def/Algebra_PointDerivations.html#L47) and $\mathrm{id}_W \otimes g$ (`hΦnat`), and pinned down on dual numbers (`hΦpin`): for every $\kappa$-valued point derivation $\delta$ and every ring homomorphism $\chi : \Gamma(X_\kappa, (\mathcal U_\kappa).U\,i_0) \to \kappa[\varepsilon]$ whose first component is $ev$ and whose second component is $\delta$, the $\kappa[\varepsilon]$-point $\tau_W$ of the image of $\Phi_\kappa(\delta)$ under $W \otimes_\kappa \kappa \cong W$ equals $\operatorname{Spec}\chi$ followed by `hU.fromSpec`.
--
--   **The endomorphism and its reductions.** $\varphi_1 : A_1 \to A_1$ is a morphism over $B_1$ (`hφ₁`), $\varphi_0 : D_0.A \to D_0.A$ a morphism over $B$ (`hφ₀f`) lifting it in the sense that $\varphi_1$ followed by $D_0.g$ equals $D_0.g$ followed by $\varphi_0$ (`hφ₀g`). The morphism $\psi : X_\kappa \to X_\kappa$ is over $\kappa$ (`hψ`), respects the base-changed group law on points — for every $T \to \operatorname{Spec}\kappa$ and all points $P, Q$, pushing the product along $\psi$ is the product of the pushes (`hψhom`) — and is the special fibre of $\varphi_0$: $\psi$ followed by `pullback.fst` equals `pullback.fst` followed by $\varphi_0$ (`hψ₀`). Its differential at the unit is recorded by a $\kappa$-linear map $\theta_\psi : W \to W$ with $\tau_W(\theta_\psi w) =$ `pushPt ψ hψ (τW w)` (`hθψ`).
--
--   **First Čech cohomology and the action of $\psi$.** $H_1$ is a $\kappa$-vector space, $cls_1 : \ker d^1 \to H_1$ is a surjective $\kappa$-linear map (`hcls₁`) whose kernel consists exactly of the cocycles lying in the range of $d^0$ (`hcls₁0`), so that $H_1$ presents the first Čech cohomology of the structure sheaf for $\mathcal U_\kappa$; and $\rho_\psi : H_1 \to H_1$ is pinned as the map induced by $\psi$ (`hρψ`): for every ordered affine cover $\mathcal V$ of $X_\kappa$, all index maps $lam, lam'$ refining $\mathcal V$ into $\mathcal U_\kappa$ along $\psi$ and along the identity respectively, and all cocycles $z, z'$, if the difference of `OModulePresheaf.unitPullback` of $z$ along $\psi$ and of $z'$ along the identity lies in the range of $d^0$ for $\mathcal V$, then $\rho_\psi(cls_1 z) = cls_1 z'$.
--
--   **Conclusion.** For every point derivation $\hat c$ of $\Gamma(X_\kappa, (\mathcal U_\kappa).U\,i_0)$ at $ev$ with values in $\operatorname{Hom}_\kappa(V^\vee, \ker d^1)$ such that $\hat c$ lifts $c$, i.e. for all $a$ and all $\xi \in V^\vee$ the cochain underlying $\hat c(a)(\xi)$ equals $c(a)(\xi)$ in $C^1$, the following two assertions are equivalent. First, there exists $\varphi : D.A \to D.A$ with $\varphi$ followed by $D.f$ equal to $D.f$ and with $\varphi_1$ followed by $D.g$ equal to $D.g$ followed by $\varphi$. Second, putting $M := \operatorname{Hom}_\kappa(V^\vee, H_1)$ and
--   $$\hat\xi := \Phi_M\bigl(\mathrm{map}\,ev\,(cls_1 \circ -)\,\hat c\bigr) \in W \otimes_\kappa M,$$
--   obtained by pushing $\hat c$ forward along post-composition with $cls_1$ and applying $\Phi$, one has
--   $$(\theta_\psi \otimes \mathrm{id}_M)\,\hat\xi \;-\; \bigl(\mathrm{id}_W \otimes (\rho_\psi \circ -)\bigr)\,\hat\xi \;=\; 0$$
--   in $W \otimes_\kappa M$.
--
--   This is the Kodaira–Spencer lifting criterion for an endomorphism, in the special case where the same deformation serves as source and target and where $\varphi_1$ is already known to lift to the base deformation $D_0$, so that the obstruction reduces to the difference $\theta_\psi \otimes 1 - 1 \otimes \rho_\psi$ applied to the tangent class of the regluing, an element of $W \otimes_\kappa \operatorname{Hom}_\kappa(V^\vee, H^1)$. It is used in the deformation-theoretic analysis of fake elliptic curves, via [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_class_bareDeformation_dualNumber_forall_isIso_iff_of_isAlgClosed_of_charP`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_class_bareDeformation_dualNumber_forall_isIso_iff_of_isAlgClosed_of_charP).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_comp_eq_comp_iff_map_tmul_sub_eq_zero_of_isRegluingBy_of_hom_bare.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing Scheme.TwoAffineOpenCover
open scoped Quaternion TensorProduct NumberField

theorem GoodReductionJacobian.BareDeformation.exists_comp_eq_comp_iff_map_tmul_sub_eq_zero_of_isRegluingBy_of_hom_bare
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [IsAlgClosed (ResidueField B)]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥)
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁) (hc₁ : L₁.IsCommutative)
    (h₁ : AbelianSchemePropertyBundle B₁ f₁)
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    [Module (ResidueField B)ᵐᵒᵖ V] [IsCentralScalar (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))

    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f]
    (𝒰 : D₀.A.OrderedAffineCover) (i₀ : 𝒰.ι) (e₀ : Spec (CommRingCat.of B) ⟶ ↑(𝒰.U i₀)) (he₀ : e₀ ≫ (𝒰.U i₀).ι = (D₀.L.one (𝟙 _)).1)

    (e₁ : Spec (CommRingCat.of (ResidueField B)) ⟶ (((𝒰.baseChange D₀.f (ResidueField B)).U i₀) : Scheme.{0}))
    (he₁ : e₁ ≫ ((𝒰.baseChange D₀.f (ResidueField B)).U i₀).ι = ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).one (𝟙 _)).1)
    (σ : ∀ s : 𝒰.Idx 1,
      letI := algebraOfHom D₀.f (𝒰.inter s)
      ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s)) ≃+* Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s))
    (hσ₁ : ∀ (s : 𝒰.Idx 1) (x : Γ(D₀.A, 𝒰.inter s)),
      letI := algebraOfHom D₀.f (𝒰.inter s)
      σ s ((1 : (ResidueField B)) ⊗ₜ[B] x) =
        ((pullback D₀.f (specMap B (ResidueField B))).presheaf.map (homOfLE (𝒰.baseChange_inter_le D₀.f (ResidueField B) s)).op).hom
          (((pullback.fst D₀.f (specMap B (ResidueField B))).app (𝒰.inter s)).hom x))
    (hσ₂ : ∀ (s : 𝒰.Idx 1) (a : (ResidueField B)),
      letI := algebraOfHom D₀.f (𝒰.inter s)
      letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).inter s)
      σ s (a ⊗ₜ[B] (1 : Γ(D₀.A, 𝒰.inter s))) = algebraMap (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s) a)
    (c : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) (((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom
          (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)))
    (hc : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ
        ∈ LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))

    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation f₁ L₁ B) (hD : D₀.IsRegluingBy 𝒰 τ D)
    (hτ : ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
            σ s (cs a ξ) = (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ s)

    (hU : IsAffineOpen ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))
    (W : Type) [AddCommGroup W] [Module (ResidueField B) W]
    (τW : W → SchemeHomOver (tangentBase (ResidueField B) (RingHom.id (ResidueField B))) (pullback.snd D₀.f (specMap B (ResidueField B))))
    (hWinj : Function.Injective τW)
    (hWrange : ∀ P : SchemeHomOver (tangentBase (ResidueField B) (RingHom.id (ResidueField B))) (pullback.snd D₀.f (specMap B (ResidueField B))), P ∈ Set.range τW ↔ IsTangentVector (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (ResidueField B) (RingHom.id (ResidueField B)) P)
    (hWadd : ∀ v w : W, τW (v + w) = (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul (tangentBase (ResidueField B) (RingHom.id (ResidueField B))) (τW v) (τW w))
    (hWsmul : ∀ (a : (ResidueField B)) (v : W), (τW (a • v)).1 = tangentScale (ResidueField B) a ≫ (τW v).1)

    (Φ : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (M : Type) [AddCommGroup M] [Module (ResidueField B) M], ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) M) ≃ₗ[(ResidueField B)] (W ⊗[(ResidueField B)] M))
    (hΦnat : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (M M' : Type) [AddCommGroup M] [Module (ResidueField B) M] [AddCommGroup M'] [Module (ResidueField B) M'] (g : M →ₗ[(ResidueField B)] M') (δ : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) M)),
        Φ M' (Algebra.PointDerivations.map ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) g δ) = TensorProduct.map (LinearMap.id : W →ₗ[(ResidueField B)] W) g (Φ M δ))
    (hΦpin : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (δ : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (ResidueField B))) (χ : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →+* DualNumber (ResidueField B)),
        (∀ a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)), TrivSqZeroExt.fst (χ a) = ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) a) →
        (∀ a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)), TrivSqZeroExt.snd (χ a) = (δ : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (ResidueField B)) a) →
        (τW (TensorProduct.rid (ResidueField B) W (Φ (ResidueField B) δ))).1 = Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec)

    (φ₁ : A₁ ⟶ A₁) (hφ₁ : φ₁ ≫ f₁ = f₁)
    (φ₀ : D₀.A ⟶ D₀.A) (hφ₀f : φ₀ ≫ D₀.f = D₀.f) (hφ₀g : φ₁ ≫ D₀.g = D₀.g ≫ φ₀)
    (ψ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ (pullback D₀.f (specMap B (ResidueField B)))) (hψ : ψ ≫ (pullback.snd D₀.f (specMap B (ResidueField B))) = (pullback.snd D₀.f (specMap B (ResidueField B))))
    (hψhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField B))) (P Q : SchemeHomOver t (pullback.snd D₀.f (specMap B (ResidueField B)))),
      pushPt ψ hψ ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul t P Q) = (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul t (pushPt ψ hψ P) (pushPt ψ hψ Q))
    (hψ₀ : ψ ≫ pullback.fst D₀.f (specMap B (ResidueField B)) = pullback.fst D₀.f (specMap B (ResidueField B)) ≫ φ₀)

    (θψ : W →ₗ[(ResidueField B)] W) (hθψ : ∀ w : W, τW (θψ w) = pushPt ψ hψ (τW w))

    (H₁ : Type) [AddCommGroup H₁] [Module (ResidueField B) H₁]
    (cls₁ : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) →ₗ[(ResidueField B)] H₁) (hcls₁ : Function.Surjective cls₁)
    (hcls₁0 : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)), cls₁ z = 0 ↔ (z : (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1) ∈ LinearMap.range ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 0))
    (ρψ : H₁ →ₗ[(ResidueField B)] H₁)
    (hρψ : ∀ (𝒱 : (pullback D₀.f (specMap B (ResidueField B))).OrderedAffineCover) (lam lam' : 𝒱.ι → (𝒰.baseChange D₀.f (ResidueField B)).ι)
        (hl : ∀ v, 𝒱.U v ≤ ψ ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam v)) (hl' : ∀ v, 𝒱.U v ≤ (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam' v))
        (z z' : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))),
        OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) ψ 𝒱 (𝒰.baseChange D₀.f (ResidueField B)) lam hl (0 + 1) z.1 -
            OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) 𝒱 (𝒰.baseChange D₀.f (ResidueField B)) lam' hl' (0 + 1) z'.1 ∈
          LinearMap.range ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d 𝒱 0) →
        ρψ (cls₁ z) = cls₁ z') :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)

    ∀ (ĉ : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))))),
      (∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        (((ĉ : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)))) a ξ : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))) :
            (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1) =
          (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ) →
      ((∃ φ : D.A ⟶ D.A, φ ≫ D.f = D.f ∧ φ₁ ≫ D.g = D.g ≫ φ) ↔
        TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁))
            (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) (Algebra.PointDerivations.map (M := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)))) (M' := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) H₁ cls₁) ĉ)) -
          TensorProduct.map (LinearMap.id : W →ₗ[(ResidueField B)] W) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) H₁ H₁ ρψ)
            (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) (Algebra.PointDerivations.map (M := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)))) (M' := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) H₁ cls₁) ĉ)) = 0) := by sorry
