-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_d_eq_unitPullback_hom_obstruction_cocycle_comp_sub_map_tmul_sub_baseChange_of_local_lifts_factor_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_d_eq_unitPullback_hom_obstruction_cocycle_comp_sub_map_tmul_sub_baseChange_of_local_lifts_factor_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/ddc1e4e2-0e36-5f8c-8fd4-dff643acc9f8
-- title:
--   Obstruction cochain of a composite endomorphism: coboundary identity
-- statement:
--   Throughout, $B$ is an Artinian local ring whose residue field $\kappa := \mathrm{ResidueField}\,B$ is algebraically closed, and $B_1$ is a $B$-algebra such that $\mathrm{algebraMap}\,B\,B_1$ is surjective (`hπ`), with nilpotent kernel (`hker`), with $\ker \cdot \mathfrak m_B = 0$ (`hsmall`) and $\ker \subseteq \mathfrak m_B$ (`hI`); thus $B \to B_1$ is a small extension. A scheme $A_1$ is given together with $f_1 : A_1 \to \operatorname{Spec} B_1$, a relative group law $L_1$ on $f_1$ over $B_1$ (a functorial multiplication, unit and inverse on $B_1$-points, with associativity, unit and inverse laws and naturality in the test scheme), the commutativity hypothesis `hc₁`, and `h₁ : AbelianSchemePropertyBundle B₁ f₁`, i.e. $f_1$ is smooth and proper with connected fibres and carries a relative group law. A finite-dimensional $\kappa$-vector space $V$, also a $B$-module compatibly with the scalar tower and with the central right action, is given together with $\iota : V \to_{B} B$ injective (`hι`) whose image is exactly $\ker(\mathrm{algebraMap}\,B\,B_1)$ viewed as a $B$-submodule (`hιI`); so $\iota$ identifies $V$ with the kernel ideal.
--
--   The deformation datum is $D_0 : \mathrm{BareDeformation}\,f_1\,L_1\,B$: a scheme $D_0.A$ with a morphism $D_0.f$ to $\operatorname{Spec} B$, a commutative relative group law $D_0.L$ over $B$, the abelian-scheme property bundle for $D_0.f$, and a morphism $D_0.g : A_1 \to D_0.A$ making the square over $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ cartesian and compatible with the group laws; $D_0.f$ is separated. Write $X_\kappa := \mathrm{pullback}\,D_0.f\,(\mathrm{specMap}\,B\,\kappa)$ for the special fibre, with its two projections, and for an ordered affine cover $\mathcal K$ of $D_0.A$ write $\mathcal K_\kappa := \mathcal K.\mathrm{baseChange}\,D_0.f\,\kappa$ for the cover of $X_\kappa$ obtained by taking preimages of the charts under the first projection.
--
--   Covers and charts: $\mathcal U$ is an ordered affine cover of $D_0.A$ (a finite linearly ordered index set $\mathcal U.\iota$, affine opens $\mathcal U.U i$ with supremum $\top$), $i_0 \in \mathcal U.\iota$ is a distinguished index, $e_0 : \operatorname{Spec} B \to \mathcal U.U i_0$ satisfies `he₀`, namely $e_0$ followed by the chart inclusion is the unit section of $D_0.L$ over the identity of $\operatorname{Spec} B$, and $e_1 : \operatorname{Spec} \kappa \to \mathcal U_\kappa.U i_0$ satisfies `he₁`, the analogous identity for the unit section of the base-changed group law $\mathrm{RelativeGroupLaw.baseChange}$ of $D_0.L$ along $\mathrm{specMap}\,B\,\kappa$. The chart $\mathcal U_\kappa.U i_0$ is affine (`hU`).
--
--   Transport: for every $1$-simplex $s$ of $\mathcal U$ (a strictly increasing pair of indices, with $\mathcal U.\mathrm{inter}\,s$ the intersection of the two charts), $\sigma s$ is a ring isomorphism $\kappa \otimes_B \Gamma(D_0.A, \mathcal U.\mathrm{inter}\,s) \cong \Gamma(X_\kappa, \mathcal U_\kappa.\mathrm{inter}\,s)$; `hσ₁` says $\sigma s(1 \otimes x)$ is the image of $x$ under the first projection's comparison map followed by restriction, and `hσ₂` says $\sigma s(a \otimes 1)$ is the structure map of $\kappa$.
--
--   Tangent presentation: $W$ is a $\kappa$-vector space with a map $\tau_W$ from $W$ to the set of $\mathrm{tangentBase}\,\kappa\,\mathrm{id}$-points of the second projection $X_\kappa \to \operatorname{Spec}\kappa$ (i.e. dual-number points), injective (`hWinj`), with image exactly the tangent vectors at the identity for the base-changed group law (`hWrange`, via `IsTangentVector`), additive for that group law (`hWadd`) and compatible with scaling through $\mathrm{tangentScale}$ (`hWsmul`). Furthermore $\Phi$ is a family, natural in the coefficient module, of $\kappa$-linear isomorphisms from the module of point derivations $\mathrm{Algebra.PointDerivations}\,\kappa\,\Gamma(X_\kappa, \mathcal U_\kappa.U i_0)\,\mathrm{ev}\,M$ — where $\mathrm{ev}$ is evaluation at $e_1$ and a point derivation is a $\kappa$-linear $D$ with $D(ab) = \mathrm{ev}(a)\,D(b) + \mathrm{ev}(b)\,D(a)$ — onto $W \otimes_\kappa M$; `hΦnat` is naturality with respect to $\mathrm{PointDerivations.map}$ and $\mathrm{id}_W \otimes g$, and `hΦpin` pins $\Phi$ down geometrically: if $\delta$ is a $\kappa$-valued point derivation and $\chi$ a ring homomorphism from $\Gamma(X_\kappa, \mathcal U_\kappa.U i_0)$ to the dual numbers over $\kappa$ whose first component is $\mathrm{ev}$ and whose second component is $\delta$, then the dual-number point $\tau_W$ of the element of $W$ corresponding to $\Phi(\kappa)\delta$ is $\operatorname{Spec}(\chi)$ followed by `hU.fromSpec`.
--
--   A morphism $j_\kappa : X_\kappa \to A_1$ is given with $j_\kappa$ followed by $D_0.g$ equal to the first projection (`hjκ`).
--
--   Outer endomorphism data: $\varphi_1 : A_1 \to A_1$ over $f_1$ (`hφ₁`); $\psi : X_\kappa \to X_\kappa$ over $\operatorname{Spec}\kappa$ (`hψ`) with $\psi$ followed by $j_\kappa$ equal to $j_\kappa$ followed by $\varphi_1$ (`hψ₁`), such that composition with $\psi$ on points is a homomorphism for the base-changed group law (`hψhom`); local lifts $m i : \mathcal U.U i \to D_0.A$ over $\operatorname{Spec} B$ (`hmf`) which lift $\varphi_1$ in the sense `hmμ`: the restriction of $D_0.g$ to $\mathcal U.U i$ followed by $m i$ equals the inclusion of $D_0.g^{-1}(\mathcal U.U i)$ followed by $\varphi_1$ and $D_0.g$. The associated obstruction datum is a point derivation $c_0$ at $\mathrm{ev}$ with values in the $\kappa$-linear maps from $\mathrm{Dual}_\kappa V$ to the degree-$1$ Čech cochains of the unit $\mathcal O$-module presheaf of the second projection for the cover $\mathcal U_\kappa$ (the presheaf $U \mapsto \Gamma(X_\kappa, U)$ with its restriction maps, a degree-$n$ cochain being a family indexed by the $n$-simplices of the cover). Hypothesis `hc₀` says that for each $1$-simplex $s$ of $\mathcal U$ there is $c_s$, with values in the $\kappa$-linear maps $\mathrm{Dual}_\kappa V \to \kappa \otimes_B \Gamma(D_0.A,\mathcal U.\mathrm{inter}\,s)$, which is a tangent-coordinate datum `IsTangentCoordsOfPairAt` for the kernel ideal, $V$, $\iota$ and $C = \Gamma(D_0.A,\mathcal U.\mathrm{inter}\,s)$ for the pair of morphisms given by the inverse of the affine isomorphism of $\mathcal U.\mathrm{inter}\,s$ followed by the two inclusions into the charts of $s$ and then by $m(s_0)$, resp. $m(s_1)$, relative to the special fibre, the base-changed group law, the first projection and the chart $\mathcal U_\kappa.U i_0$ — that is, there are a point of the thickening $(\kappa \otimes_B C) \otimes_\kappa (\kappa \oplus V)$ over the tangent base and a lift into the chart of its translate by the group law whose tangent coordinates are $c_s$, the underlying point being a tangent-of-pair datum for the two morphisms — and moreover $\sigma s \circ c_s$ agrees with the $s$-component of $c_0$ at every $a$ and $\xi$. Hypothesis `hc₀Z` says that the degree-$1$ Čech coboundary of $c_0.1\,a\,\xi$ vanishes for all $a$ and $\xi$. Finally $\theta_\psi : W \to W$ is $\kappa$-linear with `hθψ`: $\tau_W(\theta_\psi w)$ is obtained from $\tau_W(w)$ by composing with $\psi$ ($\mathrm{pushPt}\,\psi\,h\psi$).
--
--   Inner endomorphism data: exactly the same package with primes, namely $\varphi_1'$ over $f_1$ (`hφ₁'`), $\psi'$ over $\operatorname{Spec}\kappa$ (`hψ'`) compatible with $\varphi_1'$ through $j_\kappa$ (`hψ₁'`) and a homomorphism for the group law (`hψhom'`), local lifts $m'$ with `hmf'`, `hmμ'`, and a point derivation $c_0'$ with the tangent-coordinate clauses `hc₀'` and the cocycle clause `hc₀Z'`. No differential of $\psi'$ on $W$ is assumed.
--
--   Composite data: $\varphi_1'' : A_1 \to A_1$ with `hcomp`: $\varphi_1''$ is $\varphi_1'$ followed by $\varphi_1$; arbitrary local lifts $m''$ with `hmf''` and `hmμ''` (the lifting condition for $\varphi_1''$), and a point derivation $c_0''$ with the tangent-coordinate clauses `hc₀''` and the cocycle clause `hc₀Z''`.
--
--   Refinement data: $\mathcal V$ is a further ordered affine cover of $D_0.A$, with index maps $\mathrm{lam}_0, \mathrm{lam}_0' : \mathcal V.\iota \to \mathcal U.\iota$ such that $\mathcal V.U v \le \mathcal U.U(\mathrm{lam}_0' v)$ (`hsub`), morphisms $n' v : \mathcal V.U v \to \mathcal U.U(\mathrm{lam}_0 v)$ with `hn'`: $n' v$ followed by the chart inclusion equals the inclusion $\mathcal V.U v \le \mathcal U.U(\mathrm{lam}_0' v)$ followed by $m'(\mathrm{lam}_0' v)$ — so $m'$ restricted to $\mathcal V.U v$ factors through the chart $\mathcal U.U(\mathrm{lam}_0 v)$ — together with the two containments on the special fibre: $\mathcal V_\kappa.U v \le \psi'^{-1}(\mathcal U_\kappa.U(\mathrm{lam}_0 v))$ (`hl₀`) and $\mathcal V_\kappa.U v \le \mathrm{id}^{-1}(\mathcal U_\kappa.U(\mathrm{lam}_0' v))$ (`hl₀'`).
--
--   Conclusion. For every section $a \in \Gamma(X_\kappa, \mathcal U_\kappa.U i_0)$ and every $\xi \in \mathrm{Dual}_\kappa V$ there exists a degree-$0$ Čech cochain $b$ of the unit $\mathcal O$-module presheaf of the second projection for the cover $\mathcal V_\kappa$ (a family of sections over the charts $\mathcal V_\kappa.U v$) whose degree-$0$ Čech coboundary equals the three-term expression
--   $$\mathrm{unitPullback}(\mathrm{id},\mathrm{lam}_0',\mathrm{hl}_0')\bigl(c_0''.1\,a\,\xi\bigr) \; - \; \mathrm{unitPullback}(\mathrm{id},\mathrm{lam}_0',\mathrm{hl}_0')\Bigl(\bigl(\Phi(M)^{-1}\bigl((\theta_\psi \otimes \mathrm{id}_M)(\Phi(M)\,c_0')\bigr)\bigr).1\,a\,\xi\Bigr) \; - \; \mathrm{unitPullback}(\psi',\mathrm{lam}_0,\mathrm{hl}_0)\bigl(c_0.1\,a\,\xi\bigr),$$
--   all three terms being degree-$1$ cochains for $\mathcal V_\kappa$; here $M$ denotes the coefficient module $\mathrm{Dual}_\kappa V \to_\kappa \bigl(\text{degree-}1\ \text{cochains for } \mathcal U_\kappa\bigr)$, and $\mathrm{unitPullback}(h,\mathrm{lam},\mathrm{hlam})$ in degree $1$ sends a cochain for $\mathcal U_\kappa$ to the cochain for $\mathcal V_\kappa$ whose value on a simplex $s$ is, when $\mathrm{lam}\circ s$ is injective, the sign of the sorting permutation times the restriction to $\mathcal V_\kappa.\mathrm{inter}\,s$ of the image under $h$ of the value on the sorted simplex, and $0$ otherwise. Thus on the refinement $\mathcal V$ the obstruction cochain of the composite is cohomologous to the sum of the $\theta_\psi$-twist of the inner cochain and the $\psi'$-pullback of the outer cochain, with the coboundary witnessed explicitly for each $a$ and $\xi$.
--
--   This is the cochain-level functoriality of the obstruction to lifting an endomorphism of $A_1$ along the small extension $B \to B_1$: the obstruction $1$-cocycle attached to a composite $\varphi_1' \circ \varphi_1$, computed from arbitrary local lifts, differs from the $\theta_\psi$-twisted inner cocycle plus the $\psi'$-pulled-back outer cocycle by an explicit Čech coboundary on a cover refining the charts through which the inner local lifts factor. It is used by [`GoodReductionJacobian.BareDeformation.map_hom_obstruction_cocycle_comp_eq_add_map_tmul_of_local_lifts_bare`](thm.html#GoodReductionJacobian.BareDeformation.map_hom_obstruction_cocycle_comp_eq_add_map_tmul_of_local_lifts_bare) to pass from this refined identity to the corresponding additivity of the obstruction classes in degree-one cohomology, within the deformation theory of abelian schemes underlying the good-reduction analysis of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_d_eq_unitPullback_hom_obstruction_cocycle_comp_sub_map_tmul_sub_baseChange_of_local_lifts_factor_bare.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_d_eq_unitPullback_hom_obstruction_cocycle_comp_sub_map_tmul_sub_baseChange_of_local_lifts_factor_bare
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

    (𝒱 : D₀.A.OrderedAffineCover) (lam₀ lam₀' : 𝒱.ι → 𝒰.ι) (hsub : ∀ v, 𝒱.U v ≤ 𝒰.U (lam₀' v))
    (n' : ∀ v : 𝒱.ι, (↑(𝒱.U v) : Scheme.{0}) ⟶ ↑(𝒰.U (lam₀ v)))
    (hn' : ∀ v, n' v ≫ (𝒰.U (lam₀ v)).ι = D₀.A.homOfLE (hsub v) ≫ m' (lam₀' v))
    (hl₀ : ∀ v, (𝒱.baseChange D₀.f (ResidueField B)).U v ≤ ψ' ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam₀ v))
    (hl₀' : ∀ v, (𝒱.baseChange D₀.f (ResidueField B)).U v ≤
      (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam₀' v)) :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
    ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      ∃ b : (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒱.baseChange D₀.f (ResidueField B)) 0,
        (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒱.baseChange D₀.f (ResidueField B)) 0 b =
          OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (c₀''.1 a ξ)
            - OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (((Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))) (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) c₀'))).1 a ξ)
            - OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) ψ' (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀ hl₀ 1 (c₀.1 a ξ) := by sorry
