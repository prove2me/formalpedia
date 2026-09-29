-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_map_hom_obstruction_cocycle_comp_eq_add_map_tmul_of_local_lifts_bare
-- name    : GoodReductionJacobian.BareDeformation.map_hom_obstruction_cocycle_comp_eq_add_map_tmul_of_local_lifts_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/c77fda68-53a5-5016-a456-3cbaa52564b1
-- title:
--   Obstruction class of a composite endomorphism
-- statement:
--   Throughout, $\kappa := \mathrm{ResidueField}\,B$ and $I := \ker(\mathrm{algebraMap}\,B\,B_1)$.
--
--   **Small extension data.** $B$ is a commutative local artinian ring whose residue field $\kappa$ is algebraically closed, $B_1$ is a commutative $B$-algebra; `hπ` says that $B \to B_1$ is surjective, `hker` that $I$ is nilpotent, `hsmall` that $I\cdot\mathfrak m_B = 0$, and `hI` that $I \subseteq \mathfrak m_B$. Further, $V$ is a finite-dimensional $\kappa$-vector space, also carrying a $B$-module structure compatible with the $\kappa$-structure and a central right $\kappa$-action, and $\iota : V \to_{B} B$ is an injective $B$-linear map (`hι`) whose range is exactly $I$ viewed as a $B$-submodule (`hιI`); thus $V$ is an identification of the ideal $I$.
--
--   **The abelian scheme over $B_1$ and its bare deformation.** $f_1 : A_1 \to \operatorname{Spec} B_1$ carries a relative group law $L_1$ (functorial multiplication, unit and inverse on points $\mathrm{SchemeHomOver}\,t\,f_1$, with associativity, unit and inverse laws and naturality in the base), assumed commutative (`hc₁`), and `h₁` is the bundle `AbelianSchemePropertyBundle B₁ f₁`: $f_1$ is smooth and proper, its fibres are connected, and it admits a relative group law. $D_0$ is a `BareDeformation f₁ L₁ B`: a scheme $D_0.A$ with a morphism $D_0.f$ to $\operatorname{Spec} B$, a commutative relative group law $D_0.L$, the corresponding abelian-scheme property bundle over $B$, and a morphism $D_0.g : A_1 \to D_0.A$ making the square over $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ cartesian and compatible with the two group laws. In addition $D_0.f$ is separated.
--
--   **Chart data.** $\mathcal U$ is an ordered affine cover of $D_0.A$ (a finite linearly ordered index set, affine opens covering $D_0.A$), $i_0$ a distinguished index, and $e_0 : \operatorname{Spec} B \to \mathcal U.U\,i_0$ satisfies (`he₀`) that $e_0$ followed by the open immersion is the unit section of $D_0.L$; $e_1$ is the analogous section of the $i_0$-th chart of the cover $\mathcal U.\mathrm{baseChange}$ of the pullback $X_\kappa := \mathrm{pullback}\,D_0.f\,(\mathrm{specMap}\,B\,\kappa)$, with (`he₁`) the unit section of the base-changed group law $\mathrm{RelativeGroupLaw.baseChange}$. For each pair index $s \in \mathcal U.\mathrm{Idx}\,1$, $\sigma\,s$ is a ring isomorphism $\kappa \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s) \cong \Gamma(X_\kappa, (\mathcal U.\mathrm{baseChange}).\mathrm{inter}\,s)$, normalised by `hσ₁` (on $1 \otimes x$ it is the pullback of $x$ along $\mathrm{pullback.fst}$ followed by restriction) and `hσ₂` (on $a \otimes 1$ it is the structure map of $\kappa$). Finally `hU` records that the $i_0$-th chart of the base-changed cover is affine open.
--
--   **Tangent space and point-derivation coordinates.** $W$ is a $\kappa$-vector space and $\tau_W$ assigns to each $w \in W$ a point of $X_\kappa$ over the dual-number base $\mathrm{tangentBase}\,\kappa\,\mathrm{id}$; `hWinj` says $\tau_W$ is injective, `hWrange` that its image consists exactly of the points $P$ with $\mathrm{IsTangentVector}$ for the base-changed law (i.e. $\mathrm{tangentZero} \circ$-composite of $P$ is the unit at the geometric point), `hWadd` that $\tau_W$ turns addition into the group-law multiplication of the base-changed law, and `hWsmul` that $\tau_W(a\cdot v)$ is $\mathrm{tangentScale}\,\kappa\,a$ followed by $\tau_W(v)$. Writing $E := \Gamma(X_\kappa, (\mathcal U.\mathrm{baseChange}).U\,i_0)$ and $\mathrm{ev} : E \to \kappa$ for the ring homomorphism obtained from $e_1$ (the composite of $\mathrm{topIso.inv}$, $e_1.\mathrm{appTop}$ and the $\Gamma$–$\operatorname{Spec}$ isomorphism), $\Phi$ is a family, indexed by $\kappa$-vector spaces $M$, of $\kappa$-linear isomorphisms from $\mathrm{Algebra.PointDerivations}\,\kappa\,E\,\mathrm{ev}\,M$ — the $\kappa$-linear maps $D : E \to M$ with $D(ab) = \mathrm{ev}(a)\,D(b) + \mathrm{ev}(b)\,D(a)$ — onto $W \otimes_\kappa M$. It is natural in $M$ (`hΦnat`: $\Phi_{M'}$ of the post-composition of $\delta$ with $g$ is $(\mathrm{id}_W \otimes g)(\Phi_M \delta)$) and geometrically pinned (`hΦpin`): for a $\kappa$-valued point derivation $\delta$ and a ring homomorphism $\chi$ from $E$ to the dual numbers over $\kappa$ whose first component is $\mathrm{ev}$ and whose second component is $\delta$, the point $\tau_W$ of the image of $\Phi_\kappa \delta$ under $W \otimes_\kappa \kappa \cong W$ has underlying morphism $\operatorname{Spec}\chi$ followed by $\mathrm{hU.fromSpec}$.
--
--   Also given is $j_\kappa : X_\kappa \to A_1$ with $j_\kappa$ followed by $D_0.g$ equal to $\mathrm{pullback.fst}$ (`hjκ`).
--
--   **Outer endomorphism data.** $\varphi_1 : A_1 \to A_1$ lies over $\operatorname{Spec} B_1$ (`hφ₁`), $\psi : X_\kappa \to X_\kappa$ lies over $\operatorname{Spec}\kappa$ (`hψ`), they are compatible via $j_\kappa$ (`hψ₁`: $\psi$ followed by $j_\kappa$ equals $j_\kappa$ followed by $\varphi_1$), and `hψhom` says that the operation $\mathrm{pushPt}\,\psi\,h\psi$ on points over any base $t \to \operatorname{Spec}\kappa$ is a homomorphism for the base-changed group law. The family $m$ gives, for each chart index $i$, a morphism $\mathcal U.U\,i \to D_0.A$ over $\operatorname{Spec} B$ (`hmf`) which lifts $\varphi_1$ in the sense of `hmμ`: the restriction of $D_0.g$ over $\mathcal U.U\,i$ followed by $m\,i$ equals the inclusion followed by $\varphi_1$ followed by $D_0.g$. The cochain datum $c_0$ is a point derivation in $\mathrm{PointDerivations}\,\kappa\,E\,\mathrm{ev}$ with values in $\mathrm{Hom}_\kappa(V^\vee, C^1)$, where $C^1$ is the degree-$1$ cochain module of the structure-sheaf presheaf $\mathrm{OModulePresheaf.unit}$ of $X_\kappa \to \operatorname{Spec}\kappa$ on the base-changed cover. Hypothesis `hc₀` says that for every pair index $s$ there is a function $c_s$ on $E$ with values in $\mathrm{Hom}_\kappa(V^\vee, \kappa \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s))$ satisfying [`AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt`](def/AlgebraicGeometry_TangentCoordsOfPairAt.html#L31) for the ideal $I$, the module $V$ with $\iota$, the ring $C := \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s)$, the two morphisms $\operatorname{Spec} C \to D_0.A$ obtained from the affine chart isomorphism of the overlap followed by the inclusions into $\mathcal U.U\,(s_0)$, $\mathcal U.U\,(s_1)$ and then $m\,(s_0)$, $m\,(s_1)$, with structure morphism $\mathrm{pullback.snd}$, the base-changed group law, $\mathrm{pullback.fst}$ and the chart $(\mathcal U.\mathrm{baseChange}).U\,i_0$ — that is, there exist a morphism $w_0$ from the spectrum of the thickening $(\kappa \otimes_B C) \otimes_\kappa (\kappa \oplus V)$ into the special fibre over the tangent base and a lift $w_1$ into the chart of the translate of $w_0$ by the group law, such that the pair of lifts is a tangent of pair in the sense of `IsTangentOfPair` and $c_s$ is the resulting tangent-coordinate function of the chart ring homomorphism of $w_1$ — and moreover $\sigma\,s$ carries $c_s(a)(\xi)$ to the $s$-component of $c_0(a)(\xi)$. Hypothesis `hc₀Z` says that all values $c_0(a)(\xi)$ are killed by the degree-$1$ differential $d$ of that presheaf, i.e. are cocycles. Finally $\theta_\psi : W \to W$ is $\kappa$-linear with $\tau_W(\theta_\psi w) = \mathrm{pushPt}\,\psi\,h\psi\,(\tau_W w)$ (`hθψ`), the differential of $\psi$ at the identity.
--
--   **Inner endomorphism data.** The primed data $\varphi_1'$, $\psi'$, $m'$, $c_0'$ satisfy exactly the corresponding hypotheses `hφ₁'`, `hψ'`, `hψ₁'`, `hψhom'`, `hmf'`, `hmμ'`, `hc₀'`, `hc₀Z'` with $\varphi_1$, $\psi$, $m$, $c_0$ replaced by their primed counterparts.
--
--   **Composite data.** $\varphi_1'' : A_1 \to A_1$ is required only to satisfy `hcomp`: $\varphi_1''$ is $\varphi_1'$ followed by $\varphi_1$. The lifts $m''$ are arbitrary subject to `hmf''` (they lie over $\operatorname{Spec} B$) and `hmμ''` (they lift $\varphi_1''$ in the same sense as above), and $c_0''$ is a point derivation with values in $\mathrm{Hom}_\kappa(V^\vee, C^1)$ satisfying the tangent-coordinate hypothesis `hc₀''` relative to $m''$ and the cocycle hypothesis `hc₀Z''`. No morphism of special fibres and no homomorphism property is imposed on the composite.
--
--   **Cohomology and the pull-back operator.** $H_1$ is a $\kappa$-vector space and $\mathrm{cls}_1$ a surjective $\kappa$-linear map (`hcls₁`) from $Z := \ker d^1$ to $H_1$ whose kernel is precisely the image of $d^0$ (`hcls₁0`); thus $H_1$ is the first Čech cohomology of the structure-sheaf presheaf on the base-changed cover. The operator $\rho_{\psi'} : H_1 \to H_1$ is pinned by `hρψ'`: for every ordered affine cover $\mathcal V$ of $X_\kappa$, every pair of index maps $\mathrm{lam}, \mathrm{lam}'$ into the base-changed cover with $\mathcal V.U\,v$ contained in the $\psi'$-preimage, respectively the identity-preimage, of the corresponding chart, and all cocycles $z, z' \in Z$: if the difference of the pull-back cochain $\mathrm{OModulePresheaf.unitPullback}$ of $z$ along $\psi'$ and that of $z'$ along the identity lies in the range of $d^0$ on $\mathcal V$, then $\rho_{\psi'}(\mathrm{cls}_1 z) = \mathrm{cls}_1 z'$.
--
--   **Conclusion.** For all point derivations $\hat c_0, \hat c_0', \hat c_0''$ in $\mathrm{PointDerivations}\,\kappa\,E\,\mathrm{ev}$ with values in $\mathrm{Hom}_\kappa(V^\vee, Z)$ such that, for every $a \in E$ and every $\xi \in V^\vee$, the image of $\hat c_0(a)(\xi)$ in $C^1$ is $c_0(a)(\xi)$, and likewise for $\hat c_0'$ with $c_0'$ and for $\hat c_0''$ with $c_0''$, the following identity holds in $W \otimes_\kappa \mathrm{Hom}_\kappa(V^\vee, H_1)$. Writing $[\,\cdot\,]$ for the operation that post-composes a point derivation's values with $\mathrm{cls}_1$ (via [`Algebra.PointDerivations.map`](def/Algebra_PointDerivations.html#L47) and `LinearMap.llcomp`) and $\Phi$ for $\Phi_{\mathrm{Hom}_\kappa(V^\vee, H_1)}$:
--   $$\Phi([\hat c_0'']) = (\theta_\psi \otimes \mathrm{id})\bigl(\Phi([\hat c_0'])\bigr) + (\mathrm{id}_W \otimes (\rho_{\psi'} \circ -))\bigl(\Phi([\hat c_0])\bigr),$$
--   where the first summand uses $\mathrm{TensorProduct.map}\,\theta_\psi\,\mathrm{id}$ and the second $\mathrm{TensorProduct.map}\,\mathrm{id}_W$ applied to post-composition with $\rho_{\psi'}$.
--
--   This is the functoriality, under composition of endomorphisms, of the obstruction class attached to a bare deformation of an abelian scheme along a small extension $B \to B_1$: the class of the composite $\varphi_1'$ followed by $\varphi_1$ is the $\theta_\psi$-twist of the class of the inner endomorphism plus the $\rho_{\psi'}$-pull-back of the class of the outer one, a Hochschild-type cocycle relation for the obstruction map. It is cited by [`GoodReductionJacobian.BareDeformation.exists_pointDerivations_forall_map_hom_obstruction_cocycle_add_sub_eq_zero_of_separabilityElement_bare`](thm.html#GoodReductionJacobian.BareDeformation.exists_pointDerivations_forall_map_hom_obstruction_cocycle_add_sub_eq_zero_of_separabilityElement_bare), where this relation is combined with a separability element to force the obstruction to vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_map_hom_obstruction_cocycle_comp_eq_add_map_tmul_of_local_lifts_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.map_hom_obstruction_cocycle_comp_eq_add_map_tmul_of_local_lifts_bare
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

    (φ₁ : A₁ ⟶ A₁) (hφ₁ : φ₁ ≫ f₁ = f₁)
    (ψ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ (pullback D₀.f (specMap B (ResidueField B)))) (hψ : ψ ≫ (pullback.snd D₀.f (specMap B (ResidueField B))) = (pullback.snd D₀.f (specMap B (ResidueField B))))
    (hψ₁ : ψ ≫ jκ = jκ ≫ φ₁)
    (hψhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField B))) (P Q : SchemeHomOver t (pullback.snd D₀.f (specMap B (ResidueField B)))),
      pushPt ψ hψ ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul t P Q) = (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul t (pushPt ψ hψ P) (pushPt ψ hψ Q))

    (m : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmf : ∀ i, m i ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f)
    (hmμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ m i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D₀.g)
    (c₀ : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))))
    (hc₀ : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 0) ≫ m (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ m (s.1 1))
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = c₀.1 a ξ s)
    (hc₀Z : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1 (c₀.1 a ξ) = 0)

    (θψ : W →ₗ[(ResidueField B)] W) (hθψ : ∀ w : W, τW (θψ w) = pushPt ψ hψ (τW w))

    (φ₁' : A₁ ⟶ A₁) (hφ₁' : φ₁' ≫ f₁ = f₁)
    (ψ' : (pullback D₀.f (specMap B (ResidueField B))) ⟶ (pullback D₀.f (specMap B (ResidueField B)))) (hψ' : ψ' ≫ (pullback.snd D₀.f (specMap B (ResidueField B))) = (pullback.snd D₀.f (specMap B (ResidueField B))))
    (hψ₁' : ψ' ≫ jκ = jκ ≫ φ₁')
    (hψhom' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField B))) (P Q : SchemeHomOver t (pullback.snd D₀.f (specMap B (ResidueField B)))),
      pushPt ψ' hψ' ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul t P Q) = (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul t (pushPt ψ' hψ' P) (pushPt ψ' hψ' Q))

    (m' : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmf' : ∀ i, m' i ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f)
    (hmμ' : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ m' i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁' ≫ D₀.g)
    (c₀' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))))
    (hc₀' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 0) ≫ m' (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ m' (s.1 1))
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = c₀'.1 a ξ s)
    (hc₀Z' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1 (c₀'.1 a ξ) = 0)

    (φ₁'' : A₁ ⟶ A₁) (hcomp : φ₁'' = φ₁' ≫ φ₁)
    (m'' : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmf'' : ∀ i, m'' i ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f)
    (hmμ'' : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ m'' i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁'' ≫ D₀.g)
    (c₀'' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))))
    (hc₀'' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 0) ≫ m'' (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ m'' (s.1 1))
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = c₀''.1 a ξ s)
    (hc₀Z'' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1 (c₀''.1 a ξ) = 0)

    (H₁ : Type) [AddCommGroup H₁] [Module (ResidueField B) H₁]
    (cls₁ : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) →ₗ[(ResidueField B)] H₁) (hcls₁ : Function.Surjective cls₁)
    (hcls₁0 : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)), cls₁ z = 0 ↔ (z : (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1) ∈ LinearMap.range ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 0))
    (ρψ' : H₁ →ₗ[(ResidueField B)] H₁)
    (hρψ' : ∀ (𝒱 : (pullback D₀.f (specMap B (ResidueField B))).OrderedAffineCover) (lam lam' : 𝒱.ι → (𝒰.baseChange D₀.f (ResidueField B)).ι)
        (hl : ∀ v, 𝒱.U v ≤ ψ' ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam v)) (hl' : ∀ v, 𝒱.U v ≤ (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam' v))
        (z z' : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))),
        OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) ψ' 𝒱 (𝒰.baseChange D₀.f (ResidueField B)) lam hl (0 + 1) z.1 -
            OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) 𝒱 (𝒰.baseChange D₀.f (ResidueField B)) lam' hl' (0 + 1) z'.1 ∈
          LinearMap.range ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d 𝒱 0) →
        ρψ' (cls₁ z) = cls₁ z')
 :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)

    ∀ (ĉ₀ ĉ₀' ĉ₀'' : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))))),
      (∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        ((ĉ₀.1 a ξ).1 : ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) = c₀.1 a ξ) →
      (∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        ((ĉ₀'.1 a ξ).1 : ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) = c₀'.1 a ξ) →
      (∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        ((ĉ₀''.1 a ξ).1 : ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) = c₀''.1 a ξ) →
      (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) (Algebra.PointDerivations.map (M := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)))) (M' := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) H₁ cls₁) ĉ₀'')) =
        TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁))
            (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) (Algebra.PointDerivations.map (M := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)))) (M' := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) H₁ cls₁) ĉ₀')) +
          TensorProduct.map (LinearMap.id : W →ₗ[(ResidueField B)] W) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) H₁ H₁ ρψ')
            (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) (Algebra.PointDerivations.map (M := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)))) (M' := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) H₁ cls₁) ĉ₀)) := by sorry
