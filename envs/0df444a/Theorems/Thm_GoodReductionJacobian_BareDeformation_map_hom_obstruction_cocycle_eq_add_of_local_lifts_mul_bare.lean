-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_map_hom_obstruction_cocycle_eq_add_of_local_lifts_mul_bare
-- name    : GoodReductionJacobian.BareDeformation.map_hom_obstruction_cocycle_eq_add_of_local_lifts_mul_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/c9a4a0c5-ee23-520e-bf79-e94686a5ad9a
-- title:
--   Additivity of the obstruction class under pointwise product
-- statement:
--   Throughout, write $\kappa :=$ `ResidueField B` and $I :=$ `RingHom.ker (algebraMap B B₁)`.
--
--   **Small extension data.** $B$ is a commutative local Artinian ring whose residue field $\kappa$ is algebraically closed, $B_1$ is a commutative $B$-algebra, and the structure map $B \to B_1$ is surjective (`hπ`) with nilpotent kernel (`hker`), the kernel satisfying $I \cdot \mathfrak m_B = 0$ (`hsmall`) and $I \subseteq \mathfrak m_B$ (`hI`).
--
--   **The abelian scheme over $B_1$.** $f_1 : A_1 \to \operatorname{Spec} B_1$ carries a relative group law $L_1$ (functorial multiplication, unit and inverse on $B_1$-points, with associativity, unit, inverse and base-change naturality axioms) which is commutative (`hc₁`), and `h₁ : AbelianSchemePropertyBundle B₁ f₁` asserts that $f_1$ is smooth and proper, has connected fibres, and admits a relative group law.
--
--   **The module $V$.** $V$ is a finite-dimensional $\kappa$-vector space, also a $B$-module compatibly (with central $\kappa^{\mathrm{op}}$-action), and $\iota : V \to B$ is an injective $B$-linear map whose image is exactly $I$, viewed as a $B$-submodule (`hι`, `hιI`).
--
--   **The bare deformation and its cover.** $D_0 :$ `BareDeformation f₁ L₁ B` consists of a scheme $D_0.A$, a separated morphism $D_0.f : D_0.A \to \operatorname{Spec} B$, a commutative relative group law $D_0.L$ on it, the abelian-scheme bundle for $D_0.f$, and a morphism $D_0.g : A_1 \to D_0.A$ making the square over $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ cartesian and compatible with the two group laws. $\mathcal U$ is an ordered affine cover of $D_0.A$: a finite linearly ordered index set $\mathcal U.\iota$ together with affine opens $\mathcal U.U i$ whose supremum is $\top$; for $n \in \mathbb N$, $\mathcal U.\mathrm{Idx}\,n$ is the set of strictly monotone $(n+1)$-tuples $s$ of indices and $\mathcal U.\mathrm{inter}\,s$ the corresponding intersection. An index $i_0$ is distinguished together with a factorisation $e_0$ of the unit section $(D_0.L.\mathrm{one}\,(\mathbf 1))_1$ through the chart $\mathcal U.U i_0$ (`he₀`), and with a factorisation $e_1$ of the unit section of the base-changed group law `RelativeGroupLaw.baseChange (specMap B κ) D₀.L` through the corresponding chart of the cover $\mathcal U.\mathrm{baseChange}\,D_0.f\,\kappa$ of the special fibre $\operatorname{pullback} D_0.f\,(\mathrm{specMap}\,B\,\kappa)$, that cover being obtained by pulling the opens $\mathcal U.U i$ back along `pullback.fst` (`he₁`). The open $(\mathcal U.\mathrm{baseChange}\,D_0.f\,\kappa).U i_0$ is assumed affine (`hU`).
--
--   **Comparison isomorphisms.** For each $s \in \mathcal U.\mathrm{Idx}\,1$, $\sigma s$ is a ring isomorphism $\kappa \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s) \cong \Gamma\bigl(\text{special fibre}, (\mathcal U.\mathrm{baseChange}\,D_0.f\,\kappa).\mathrm{inter}\,s\bigr)$; the hypotheses `hσ₁` and `hσ₂` identify it as the canonical map, namely on $1 \otimes x$ it is the pullback of $x$ along `pullback.fst` followed by restriction to the base-changed intersection, and on $a \otimes 1$ it is the structure map of $\kappa$.
--
--   **Tangent space of the special fibre at the unit.** $W$ is a $\kappa$-vector space with an injective map $\tau_W$ (`hWinj`) into the morphisms from the dual-number base $\mathrm{tangentBase}\,\kappa\,\mathrm{id}$ over `pullback.snd`, whose image consists exactly of the tangent vectors of the base-changed group law, i.e. those $P$ with $\mathrm{tangentZero}\,\kappa$ followed by $P$ equal to the unit section (`hWrange`); $\tau_W$ carries addition in $W$ to the group law (`hWadd`) and scalar multiplication by $a$ to precomposition with $\mathrm{tangentScale}\,\kappa\,a$, that is, $\tau_W(a \cdot v)$ is $\mathrm{tangentScale}\,\kappa\,a$ followed by $\tau_W v$ (`hWsmul`).
--
--   **The identification $\Phi$.** Let $\mathrm{ev} : \Gamma(\text{special fibre}, (\mathcal U.\mathrm{baseChange}\,D_0.f\,\kappa).U i_0) \to \kappa$ be the ring homomorphism obtained from $e_1$. For every $\kappa$-vector space $M$, $\Phi M$ is a $\kappa$-linear isomorphism from the module [`Algebra.PointDerivations κ Γ(…, U i₀) ev M`](def/Algebra_PointDerivations.html#L9) — the $\kappa$-linear maps $D$ with $D(ab) = \mathrm{ev}(a)\cdot D(b) + \mathrm{ev}(b)\cdot D(a)$ — onto $W \otimes_\kappa M$. The family is natural in $M$ (`hΦnat`: post-composing a derivation with $g : M \to M'$ corresponds to $\mathrm{id}_W \otimes g$), and is pinned down at $M = \kappa$ by `hΦpin`: whenever $\chi$ is a ring homomorphism from that section ring to the dual numbers $\kappa[\varepsilon]$ whose first component is $\mathrm{ev}$ and whose second component is the derivation $\delta$, the tangent vector $\tau_W$ of the image of $\Phi\,\kappa\,\delta$ under $W \otimes_\kappa \kappa \cong W$ is $\operatorname{Spec}\chi$ followed by `hU.fromSpec`.
--
--   **Degree-one cohomology handles.** $H_1$ is a $\kappa$-vector space and $\mathrm{cls}_1$ a $\kappa$-linear map from the kernel of the degree-one Čech differential $d^1$ of the presheaf `OModulePresheaf.unit (pullback.snd …)` (the structure sheaf regarded as a module presheaf) for the cover of the special fibre, onto $H_1$ (`hcls₁`), whose vanishing locus is exactly the image of $d^0$ (`hcls₁0`). Thus $H_1$ is the first Čech cohomology of the structure sheaf of the special fibre for this cover.
--
--   **The three endomorphisms.** $\varphi_1, \varphi_1', \varphi_1''$ are endomorphisms of $A_1$ over $\operatorname{Spec} B_1$ (`hφ₁`, `hφ₁'`, `hφ₁''`), and `hadd` states that $\varphi_1''$ is the pointwise $L_1$-product of the other two: for every scheme $T$, every $t : T \to \operatorname{Spec} B_1$ and every $T$-point $P$ of $f_1$, the composite $P$ followed by $\varphi_1''$ is the $L_1$-product of $P$ followed by $\varphi_1$ and $P$ followed by $\varphi_1'$.
--
--   **Local lifts and obstruction cochains.** Three families of data are given, one for each of $\varphi_1, \varphi_1', \varphi_1''$, of identical shape. For $\varphi_1$: morphisms $m i : \mathcal U.U i \to D_0.A$ over $\operatorname{Spec} B$ (`hmf`) which lift $\varphi_1$ in the sense that on $D_0.g^{-1}(\mathcal U.U i)$ the restriction of $D_0.g$ followed by $m i$ agrees with the inclusion followed by $\varphi_1$ and $D_0.g$ (`hmμ`); a point derivation $c_0$ on $\Gamma(\text{special fibre}, (\mathcal U.\mathrm{baseChange}\,D_0.f\,\kappa).U i_0)$ at $\mathrm{ev}$ with values in $\operatorname{Hom}_\kappa\bigl(V^\vee, C^1\bigr)$, where $C^1 =$ `(OModulePresheaf.unit …).cochain (𝒰.baseChange D₀.f κ) 1` is the module of $1$-cochains; the hypothesis `hc₀` requires, for each $s \in \mathcal U.\mathrm{Idx}\,1$, a function $c_s$ from that section ring to $\operatorname{Hom}_\kappa(V^\vee, \kappa \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s))$ which is a system of tangent coordinates, in the sense of [`AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt`](def/AlgebraicGeometry_TangentCoordsOfPairAt.html#L31) for the ideal $I$, the module $V$, the map $\iota$ and the ring $C = \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s)$, for the pair of morphisms $\operatorname{Spec} C \to D_0.A$ obtained from the inverse of the canonical isomorphism of the affine open $\mathcal U.\mathrm{inter}\,s$ with its spectrum followed by the inclusions into $\mathcal U.U(s_0)$, resp. $\mathcal U.U(s_1)$, and then by $m(s_0)$, resp. $m(s_1)$ — relative to the special fibre `pullback.snd`, the base-changed group law, the projection `pullback.fst` and the chart $(\mathcal U.\mathrm{baseChange}\,D_0.f\,\kappa).U i_0$; that is, there are a point $w_0$ of the special fibre with values in the thickening $(\kappa \otimes_B C) \otimes_\kappa (\kappa \oplus V)$ lying over the tangent base, such that $w_0$ followed by `pullback.fst` is a tangent vector of the pair in the sense of `IsTangentOfPair` (it factors through a Schlessinger-type homomorphism out of the pair ring of $I$ and $C$), a factorisation $w_1$ through the chart of the translate of $w_0$ to the unit, and $c_s$ is the tangent-coordinate function of the ring homomorphism $\Gamma \to$ thickening determined by $w_1$; moreover $\sigma s \circ c_s$ agrees with the $s$-component of $c_0$ evaluated at every section $a$ and every $\xi \in V^\vee$. The hypothesis `hc₀Z` says that every value $c_0(a)(\xi)$ is a Čech $1$-cocycle, i.e. is annihilated by $d^1$. The data $m', c_0'$ with `hmf'`, `hmμ'`, `hc₀'`, `hc₀Z'` are the same for $\varphi_1'$, and $m'', c_0''$ with `hmf''`, `hmμ''`, `hc₀''`, `hc₀Z''` the same for $\varphi_1''$. Finally `hm''` requires that $m''$ be the pointwise $D_0.L$-product of $m$ and $m'$ on each chart: for every $i$, $m'' i = (D_0.L.\mathrm{mul}\,((\mathcal U.U i).\iota \circ\!\!\!\!\!\!\! \text{ }D_0.f)\,\langle m i\rangle\,\langle m' i\rangle)_1$, the multiplication being taken over the base morphism $(\mathcal U.U i).\iota$ followed by $D_0.f$.
--
--   **Conclusion.** For all point derivations $\hat c_0, \hat c_0', \hat c_0''$ on $\Gamma(\text{special fibre}, (\mathcal U.\mathrm{baseChange}\,D_0.f\,\kappa).U i_0)$ at $\mathrm{ev}$ with values in $\operatorname{Hom}_\kappa(V^\vee, \ker d^1)$ whose underlying $C^1$-valued derivations are $c_0$, $c_0'$ and $c_0''$ respectively — that is, for every section $a$ and every $\xi \in V^\vee$ the cochain underlying $\hat c_0(a)(\xi)$ is $c_0(a)(\xi)$, and likewise for the primed and doubly primed data — one has
--   $$\Phi\bigl(\mathrm{cls}_{1*}\,\hat c_0''\bigr) = \Phi\bigl(\mathrm{cls}_{1*}\,\hat c_0\bigr) + \Phi\bigl(\mathrm{cls}_{1*}\,\hat c_0'\bigr)$$
--   in $W \otimes_\kappa \operatorname{Hom}_\kappa(V^\vee, H_1)$, where $\mathrm{cls}_{1*}$ denotes [`Algebra.PointDerivations.map`](def/Algebra_PointDerivations.html#L47) applied to post-composition with $\mathrm{cls}_1$ (the map `LinearMap.llcomp` of $\operatorname{Hom}_\kappa(V^\vee, \ker d^1) \to \operatorname{Hom}_\kappa(V^\vee, H_1)$) and $\Phi$ is taken at $M = \operatorname{Hom}_\kappa(V^\vee, H_1)$.
--
--   This is the additivity of the deformation-theoretic obstruction class: for a small extension $B \to B_1$ and an endomorphism of the reduction $A_1$, the class in $W \otimes_\kappa \operatorname{Hom}_\kappa(V^\vee, H^1)$ measuring the failure of local lifts to glue is additive in the endomorphism for the pointwise group-law product. It is used in the proof of [`GoodReductionJacobian.BareDeformation.exists_pointDerivations_forall_map_hom_obstruction_cocycle_add_sub_eq_zero_of_separabilityElement_bare`](thm.html#GoodReductionJacobian.BareDeformation.exists_pointDerivations_forall_map_hom_obstruction_cocycle_add_sub_eq_zero_of_separabilityElement_bare), where the obstruction is made to vanish for a suitable combination of endomorphisms of a bare deformation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_map_hom_obstruction_cocycle_eq_add_of_local_lifts_mul_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.map_hom_obstruction_cocycle_eq_add_of_local_lifts_mul_bare
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

    (H₁ : Type) [AddCommGroup H₁] [Module (ResidueField B) H₁]
    (cls₁ : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) →ₗ[(ResidueField B)] H₁) (hcls₁ : Function.Surjective cls₁)
    (hcls₁0 : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)), cls₁ z = 0 ↔ (z : (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1) ∈ LinearMap.range ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 0))

    (φ₁ φ₁' φ₁'' : A₁ ⟶ A₁) (hφ₁ : φ₁ ≫ f₁ = f₁) (hφ₁' : φ₁' ≫ f₁ = f₁) (hφ₁'' : φ₁'' ≫ f₁ = f₁)
    (hadd : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₁)) (P : SchemeHomOver t f₁),
      P.1 ≫ φ₁'' = (L₁.mul t ⟨P.1 ≫ φ₁, by rw [Category.assoc, hφ₁, P.2]⟩ ⟨P.1 ≫ φ₁', by rw [Category.assoc, hφ₁', P.2]⟩).1)

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
    (hm'' : ∀ i : 𝒰.ι, m'' i = (D₀.L.mul ((𝒰.U i).ι ≫ D₀.f) ⟨m i, hmf i⟩ ⟨m' i, hmf' i⟩).1) :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)

    ∀ (ĉ₀ ĉ₀' ĉ₀'' : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))))),
      (∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        ((ĉ₀.1 a ξ).1 : ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) = c₀.1 a ξ) →
      (∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        ((ĉ₀'.1 a ξ).1 : ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) = c₀'.1 a ξ) →
      (∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        ((ĉ₀''.1 a ξ).1 : ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) = c₀''.1 a ξ) →
      (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) (Algebra.PointDerivations.map (M := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)))) (M' := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) H₁ cls₁) ĉ₀'')) =
        (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) (Algebra.PointDerivations.map (M := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)))) (M' := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) H₁ cls₁) ĉ₀)) +
          (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁) (Algebra.PointDerivations.map (M := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)))) (M' := (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] H₁)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (LinearMap.llcomp (ResidueField B) (Module.Dual (ResidueField B) V) ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1)) H₁ cls₁) ĉ₀')) := by sorry
