-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_pointDerivations_forall_map_hom_obstruction_cocycle_add_sub_eq_zero_of_separabilityElement_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_pointDerivations_forall_map_hom_obstruction_cocycle_add_sub_eq_zero_of_separabilityElement_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/daf53199-bad5-59e3-bf65-96864e01499e
-- title:
--   Separability element trivialises the obstruction cocycle
-- statement:
--   Throughout, $k$ denotes the residue field of $B$, $X_k$ the special fibre $\mathrm{pullback}(D_0.f,\ \operatorname{Spec} k \to \operatorname{Spec} B)$ of the deformation, and $\mathcal U_k := \mathcal U.\mathrm{baseChange}\,D_0.f\,k$ the cover of $X_k$ whose charts are the preimages under `pullback.fst` of the charts of $\mathcal U$; sections over the charts carry the algebra structures induced by the structure morphisms (`algebraOfHom`).
--
--   *Base data.* $B$ is a commutative local Artinian ring with algebraically closed residue field $k$, and $B_1$ a commutative $B$-algebra such that $\mathrm{algebraMap}\,B\,B_1$ is surjective (`hπ`), its kernel $I$ is nilpotent (`hker`), satisfies $I\cdot\mathfrak m_B = 0$ (`hsmall`) and $I \le \mathfrak m_B$ (`hI`): a small extension. Over $\operatorname{Spec} B_1$ there is given $f_1 : A_1 \to \operatorname{Spec} B_1$ with a relative group law $L_1$ (a functorial group structure on $T$-points over $\operatorname{Spec} B_1$), commutative (`hc₁`), and `h₁ : AbelianSchemePropertyBundle B₁ f₁`, i.e. $f_1$ is smooth and proper, all its fibres are connected, and a relative group law on $f_1$ exists. The ideal $I$ is coordinatised by a finite-dimensional $k$-vector space $V$ (also a $B$-module through the scalar tower, with central right $k$-action) together with an injective $B$-linear $\iota : V \to B$ whose range is $I$ viewed as a $B$-submodule (`hι`, `hιI`).
--
--   *The deformation and its charts.* $D_0$ is a `BareDeformation` of $(f_1,L_1)$ to $B$: a scheme $D_0.A$ with $D_0.f : D_0.A \to \operatorname{Spec} B$, a commutative relative group law $D_0.L$, the abelian-scheme property bundle for $D_0.f$, and a morphism $D_0.g : A_1 \to D_0.A$ exhibiting $f_1$ as the base change of $D_0.f$ along $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ and compatible with the two group laws; $D_0.f$ is separated. $\mathcal U$ is an ordered affine cover of $D_0.A$ (a finite linearly ordered index type, affine opens with supremum $\top$), $i_0$ an index, and $e_0$ a $B$-point of the chart $U_{i_0}$ whose composite with the open immersion is the identity section of $D_0.L$ (`he₀`). Likewise $e_1$ is a $k$-point of the chart $\mathcal U_k.U_{i_0}$ whose composite with the open immersion is the identity section of the base-changed group law `RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L` (`he₁`), and `hU` states that $\mathcal U_k.U_{i_0}$ is affine. For each strictly monotone pair $s \in \mathcal U.\mathrm{Idx}\,1$, $\sigma_s$ is a ring isomorphism $k \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s) \cong \Gamma(X_k, \mathcal U_k.\mathrm{inter}\,s)$ between the base change of the sections over the intersection and the sections over the corresponding intersection in $X_k$, pinned by `hσ₁` on elements $1 \otimes x$ (restriction of the pullback of $x$ along `pullback.fst`) and by `hσ₂` on elements $a \otimes 1$ (the structure map of $k$).
--
--   *The tangent space at the identity.* $W$ is a $k$-vector space with a map $\tau_W$ into the morphisms $\operatorname{Spec} k[\varepsilon] \to X_k$ over `tangentBase`, which is injective (`hWinj`), has as range exactly the `IsTangentVector`s for the base-changed group law, i.e. those $P$ with $\mathrm{tangentZero} \gg P$ the identity section over the geometric point (`hWrange`), is additive for the group-law multiplication of tangent points (`hWadd`) and $k$-homogeneous through `tangentScale` (`hWsmul`). $\Phi$ assigns to every $k$-vector space $M$ a $k$-linear isomorphism from the module [`Algebra.PointDerivations`](def/Algebra_PointDerivations.html#L9) of $k$-linear maps $\delta$ on $\Gamma(X_k, \mathcal U_k.U_{i_0})$ satisfying $\delta(ab) = \mathrm{ev}(a)\delta(b) + \mathrm{ev}(b)\delta(a)$, where $\mathrm{ev}$ is the evaluation ring homomorphism at $e_1$, onto $W \otimes_k M$; `hΦnat` makes $\Phi$ natural in $M$ with respect to [`Algebra.PointDerivations.map`](def/Algebra_PointDerivations.html#L47) and $\mathrm{id}_W \otimes {-}$, and `hΦpin` pins $\Phi$ for $M = k$: for every such $\delta$ and every ring homomorphism $\chi$ into the dual numbers over $k$ whose first component is $\mathrm{ev}$ and whose second component is $\delta$, the tangent vector $\tau_W$ of the element of $W$ corresponding to $\Phi(k)\delta$ under $W \otimes_k k \cong W$ equals $\operatorname{Spec}(\chi)$ followed by `hU.fromSpec`. Finally $j_\kappa : X_k \to A_1$ satisfies $j_\kappa \gg D_0.g = \mathrm{pullback.fst}$ (`hjκ`).
--
--   *The acting ring.* $\Lambda$ is a ring and $e_\Lambda \in (k \otimes_{\mathbb Z} \Lambda) \otimes_k (k \otimes_{\mathbb Z} \Lambda)$ a separability element: multiplication carries it to $1$ (`heΛ₁`) and it is balanced under left and right multiplication by any $x \in k \otimes_{\mathbb Z}\Lambda$ (`heΛ₂`). The action upstairs is $\mathrm{act}_1 : \Lambda \to (A_1 \to A_1)$ with: each $\mathrm{act}_1 x$ over $f_1$ (`act₁_over`); each $\mathrm{act}_1 x$ a homomorphism for $L_1$ on points (`act₁_hom`); $\mathrm{act}_1 1 = \mathrm{id}$ (`act₁_one`); $\mathrm{act}_1(xy) = \mathrm{act}_1 x \circ \mathrm{act}_1 y$ (`act₁_mul`, written diagrammatically as $\mathrm{act}_1 y$ followed by $\mathrm{act}_1 x$); and additivity on points, $P \gg \mathrm{act}_1(x+y)$ being the $L_1$-product of $P \gg \mathrm{act}_1 x$ and $P \gg \mathrm{act}_1 y$ (`act₁_add`). On the special fibre, $\psi : \Lambda \to \mathrm{End}(X_k)$ consists of endomorphisms over $\operatorname{Spec} k$ (`hψ`) compatible with $\mathrm{act}_1$ through $j_\kappa$, namely $\psi x \gg j_\kappa = j_\kappa \gg \mathrm{act}_1 x$ (`hψ₁`), and acting by group-law homomorphisms on points via `pushPt` (`hψhom`).
--
--   *Local lifts and their cochains.* For each $x \in \Lambda$ and each chart index $i$, $m\,x\,i : U_i \to D_0.A$ is a morphism over $\operatorname{Spec} B$ (`hmf`) which lifts $\mathrm{act}_1 x$ on the $B_1$-fibre: restricting $D_0.g$ to $U_i$ and composing with $m\,x\,i$ gives the open immersion followed by $\mathrm{act}_1 x$ followed by $D_0.g$ (`hmμ`). The family $c_0$ assigns to each $x \in \Lambda$ a point derivation at $e_1$ with values in $\mathrm{Hom}_k\bigl(V^\vee, \check C^1\bigr)$, where $\check C^1 = (\mathrm{OModulePresheaf.unit}\,\mathrm{pullback.snd}).\mathrm{cochain}\ \mathcal U_k\ 1$ is the module of degree-one Čech cochains of the structure sheaf for the cover $\mathcal U_k$. The hypothesis `hc₀` requires, for every $x$ and every pair index $s$, a local coordinate function $c_s$ on $\Gamma(X_k,\mathcal U_k.U_{i_0})$ with values in $\mathrm{Hom}_k(V^\vee, k \otimes_B \Gamma(D_0.A,\mathcal U.\mathrm{inter}\,s))$ satisfying [`AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt`](def/AlgebraicGeometry_TangentCoordsOfPairAt.html#L31) for the ideal $I$, the data $(V,\iota)$, the ring $\Gamma(D_0.A,\mathcal U.\mathrm{inter}\,s)$, the two morphisms obtained from the inverse of the canonical isomorphism of the affine intersection with its spectrum followed by the inclusions of the intersection into the charts $U_{s(0)}$, $U_{s(1)}$ and then by $m\,x\,(s(0))$, $m\,x\,(s(1))$, and the special-fibre data ($X_k$ over $\operatorname{Spec} k$, the base-changed group law, `pullback.fst`, the chart $\mathcal U_k.U_{i_0}$); that predicate asserts the existence of a morphism $w_0$ from the spectrum of the thickening ring $(k \otimes_B C) \otimes_k (k \oplus V)$ to $X_k$ over the relative tangent base and a morphism $w_1$ into the chart such that $w_0$ followed by `pullback.fst` is a tangent vector of the pair of lifts in the sense of `IsTangentOfPair` (a Schlessinger map out of the pair ring of $I$ and $C$ through which the two morphisms factor), $w_1$ followed by the open immersion is the translate of $w_0$ to the identity section of the base-changed group law, and $c_s$ is the `tangentCoords` of the ring homomorphism induced by $w_1$ on the sections of the chart. In addition `hc₀` demands $\sigma_s(c_s(a)(\xi)) = (c_0 x)(a)(\xi)(s)$ for all $a$ and all $\xi \in V^\vee$, so that $c_0 x$ records these local coordinates as a Čech $1$-cochain; and `hc₀Z` demands that every $(c_0 x)(a)(\xi)$ be annihilated by the Čech differential $d^1$ of $\mathcal U_k$.
--
--   *The two actions on cohomology.* $\theta_\Lambda : \Lambda \to \mathrm{End}_k W$ is a ring homomorphism pinned by $\tau_W(\theta_\Lambda x\, w) = \mathrm{pushPt}(\psi x)(\tau_W w)$ (`hθΛ`), i.e. it is the action of $\psi$ on tangent vectors at the identity. $H_1$ is a $k$-vector space with a surjective $k$-linear map $\mathrm{cls}_1$ from the $1$-cocycles $\ker d^1$ onto $H_1$ (`hcls₁`) whose kernel is exactly the coboundaries, the range of $d^0$ (`hcls₁0`); thus $H_1$ is the first Čech cohomology of the structure sheaf for $\mathcal U_k$. Finally $\rho_\Lambda : \Lambda^{\mathrm{op}} \to \mathrm{End}_k H_1$ is a ring homomorphism pinned by `hρΛ`: for every $x \in \Lambda$, every ordered affine cover $\mathcal V$ of $X_k$, index maps $\mathrm{lam}, \mathrm{lam}'$ with $\mathcal V.U_v$ contained in the $\psi x$-preimage, respectively the identity-preimage, of the corresponding chart of $\mathcal U_k$, and all $1$-cocycles $z, z'$, if the difference of `OModulePresheaf.unitPullback` of $z$ along $\psi x$ and of $z'$ along the identity is a coboundary on $\mathcal V$, then $\rho_\Lambda(\mathrm{op}\,x)(\mathrm{cls}_1 z) = \mathrm{cls}_1 z'$; so $\rho_\Lambda(\mathrm{op}\,x)$ is pullback along $\psi x$ on $H_1$.
--
--   *Conclusion.* There exists a point derivation $c$ at $e_1$ on $\Gamma(X_k,\mathcal U_k.U_{i_0})$ with values in $\mathrm{Hom}_k(V^\vee, \check C^1)$ such that both of the following hold.
--
--   First, $c$ is cocycle-valued: for every section $a$ of the chart and every $\xi \in V^\vee$, the cochain $c(a)(\xi)$ lies in $\ker d^1$.
--
--   Second, for every $x \in \Lambda$ and every pair $\hat c, \hat c_0$ of point derivations at $e_1$ with values in $\mathrm{Hom}_k(V^\vee, \ker d^1)$ such that $\hat c_0$ lifts $c_0 x$ and $\hat c$ lifts $c$ — meaning that for all $a$ and $\xi$ the underlying cochains of $\hat c_0(a)(\xi)$ and $\hat c(a)(\xi)$ are $(c_0 x)(a)(\xi)$ and $c(a)(\xi)$ respectively — the following identity holds in $W \otimes_k \mathrm{Hom}_k(V^\vee, H_1)$:
--   $$\Phi\bigl(\mathrm{cls}_1 \circ \hat c_0\bigr) + (\theta_\Lambda x \otimes \mathrm{id})\,\Phi\bigl(\mathrm{cls}_1 \circ \hat c\bigr) - \bigl(\mathrm{id}_W \otimes (\rho_\Lambda(\mathrm{op}\,x) \circ {-})\bigr)\,\Phi\bigl(\mathrm{cls}_1 \circ \hat c\bigr) = 0,$$
--   where $\mathrm{cls}_1 \circ {-}$ denotes [`Algebra.PointDerivations.map`](def/Algebra_PointDerivations.html#L47) applied to postcomposition with $\mathrm{cls}_1$ (`LinearMap.llcomp`), carrying derivations valued in $\mathrm{Hom}_k(V^\vee,\ker d^1)$ to derivations valued in $\mathrm{Hom}_k(V^\vee, H_1)$, and $\Phi$ is taken with $M = \mathrm{Hom}_k(V^\vee, H_1)$.
--
--   This is the Hochschild-style vanishing step in the deformation theory of an abelian scheme equipped with an action of a ring $\Lambda$: the obstruction to lifting the $\Lambda$-action to the bare deformation $D_0$ is a one-cocycle on $\Lambda$ with values in the $(k\otimes_{\mathbb Z}\Lambda)$-bimodule $W \otimes_k \mathrm{Hom}_k(V^\vee, H^1)$, and the existence of a separability element for $k \otimes_{\mathbb Z}\Lambda$ forces that cocycle to be a coboundary, realised here by an honest cocycle-valued point derivation $c$ representing the required re-gluing class. It is used by [`GoodReductionJacobian.BareDeformation.exists_forall_exists_comp_eq_comp_of_separabilityElement_of_ker_mul_maximalIdeal_eq_bot`](thm.html#GoodReductionJacobian.BareDeformation.exists_forall_exists_comp_eq_comp_of_separabilityElement_of_ker_mul_maximalIdeal_eq_bot), where the re-glued deformation carries a genuine lift of every $\mathrm{act}_1 x$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_pointDerivations_forall_map_hom_obstruction_cocycle_add_sub_eq_zero_of_separabilityElement_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_pointDerivations_forall_map_hom_obstruction_cocycle_add_sub_eq_zero_of_separabilityElement_bare
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

    (jκ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ A₁) (hjκ : jκ ≫ D₀.g = (pullback.fst D₀.f (specMap B (ResidueField B))))

    (Λ : Type) [Ring Λ]
    (eΛ : ((ResidueField B) ⊗[ℤ] Λ) ⊗[(ResidueField B)] ((ResidueField B) ⊗[ℤ] Λ))
    (heΛ₁ : LinearMap.mul' (ResidueField B) ((ResidueField B) ⊗[ℤ] Λ) eΛ = 1)
    (heΛ₂ : ∀ x : (ResidueField B) ⊗[ℤ] Λ, TensorProduct.map (LinearMap.mulLeft (ResidueField B) x) LinearMap.id eΛ =
      TensorProduct.map LinearMap.id (LinearMap.mulRight (ResidueField B) x) eΛ)

    (act₁ : Λ → (A₁ ⟶ A₁)) (act₁_over : ∀ x : Λ, act₁ x ≫ f₁ = f₁)
    (act₁_hom : ∀ (x : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₁)) (P Q : SchemeHomOver t f₁),
      (L₁.mul t P Q).1 ≫ act₁ x =
        (L₁.mul t ⟨P.1 ≫ act₁ x, by rw [Category.assoc, act₁_over, P.2]⟩
          ⟨Q.1 ≫ act₁ x, by rw [Category.assoc, act₁_over, Q.2]⟩).1)
    (act₁_one : act₁ 1 = 𝟙 A₁)
    (act₁_mul : ∀ x y : Λ, act₁ (x * y) = act₁ y ≫ act₁ x)
    (act₁_add : ∀ (x y : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₁)) (P : SchemeHomOver t f₁),
      P.1 ≫ act₁ (x + y) =
        (L₁.mul t ⟨P.1 ≫ act₁ x, by rw [Category.assoc, act₁_over, P.2]⟩
          ⟨P.1 ≫ act₁ y, by rw [Category.assoc, act₁_over, P.2]⟩).1)

    (ψ : Λ → ((pullback D₀.f (specMap B (ResidueField B))) ⟶ (pullback D₀.f (specMap B (ResidueField B)))))
    (hψ : ∀ x : Λ, ψ x ≫ (pullback.snd D₀.f (specMap B (ResidueField B))) = (pullback.snd D₀.f (specMap B (ResidueField B))))
    (hψ₁ : ∀ x : Λ, ψ x ≫ jκ = jκ ≫ act₁ x)
    (hψhom : ∀ (x : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField B))) (P Q : SchemeHomOver t (pullback.snd D₀.f (specMap B (ResidueField B)))),
      pushPt (ψ x) (hψ x) ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul t P Q) = (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul t (pushPt (ψ x) (hψ x) P) (pushPt (ψ x) (hψ x) Q))

    (m : ∀ (x : Λ) (i : 𝒰.ι), (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmf : ∀ (x : Λ) (i : 𝒰.ι), m x i ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f)
    (hmμ : ∀ (x : Λ) (i : 𝒰.ι), morphismRestrict D₀.g (𝒰.U i) ≫ m x i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ act₁ x ≫ D₀.g)
    (c₀ : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      Λ → ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))))
    (hc₀ : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (x : Λ) (s : 𝒰.Idx 1),
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 0) ≫ m x (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ m x (s.1 1))
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = (c₀ x).1 a ξ s)
    (hc₀Z : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (x : Λ) (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1 ((c₀ x).1 a ξ) = 0)

    (θΛ : Λ →+* Module.End (ResidueField B) W) (hθΛ : ∀ (x : Λ) (w : W), τW (θΛ x w) = pushPt (ψ x) (hψ x) (τW w))

    (H₁ : Type) [AddCommGroup H₁] [Module (ResidueField B) H₁]
    (cls₁ : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) →ₗ[(ResidueField B)] H₁) (hcls₁ : Function.Surjective cls₁)
    (hcls₁0 : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)), cls₁ z = 0 ↔ (z : (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1) ∈ LinearMap.range ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 0))

    (ρΛ : Λᵐᵒᵖ →+* Module.End (ResidueField B) H₁)
    (hρΛ : ∀ (x : Λ) (𝒱 : (pullback D₀.f (specMap B (ResidueField B))).OrderedAffineCover) (lam lam' : 𝒱.ι → (𝒰.baseChange D₀.f (ResidueField B)).ι)
        (hl : ∀ v, 𝒱.U v ≤ ψ x ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam v)) (hl' : ∀ v, 𝒱.U v ≤ (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam' v))
        (z z' : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))),
        OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (ψ x) 𝒱 (𝒰.baseChange D₀.f (ResidueField B)) lam hl (0 + 1) z.1 -
            OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) 𝒱 (𝒰.baseChange D₀.f (ResidueField B)) lam' hl' (0 + 1) z'.1 ∈
          LinearMap.range ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d 𝒱 0) →
        ρΛ (MulOpposite.op x) (cls₁ z) = cls₁ z')
 :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
    ∃ c : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))),
      (∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))) a ξ
          ∈ LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) ∧

      ∀ (x : Λ) (ĉ ĉ₀ : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))))),
      (∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        ((ĉ₀.1 a ξ).1 : ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) = (c₀ x).1 a ξ) →
      (∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        ((ĉ.1 a ξ).1 : ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) = c.1 a ξ) →
        (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) (Algebra.PointDerivations.map (M := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)))) (M' := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) H₁ cls₁) ĉ₀)) +
          (TensorProduct.map (θΛ x) (LinearMap.id : (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁))
              (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) (Algebra.PointDerivations.map (M := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)))) (M' := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) H₁ cls₁) ĉ)) -
            TensorProduct.map (LinearMap.id : W →ₗ[(ResidueField B)] W) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) H₁ H₁ (ρΛ (MulOpposite.op x)))
              (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) (Algebra.PointDerivations.map (M := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)))) (M' := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) H₁ cls₁) ĉ))) = 0 := by sorry
