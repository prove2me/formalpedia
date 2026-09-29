-- Prove2me | Theorems.Thm_ModularCurve_XOneP_normFreePartFamily_toPic0Pair_sp_fst_smul_of_isFrobeniusAt_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.normFreePartFamily_toPic0Pair_sp_fst_smul_of_isFrobeniusAt_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/593d0688-e15c-505f-b9ac-057af2b3bc17
-- title:
--   Frobenius acts coefficientwise on the first Igusa component
-- statement:
--   Throughout, $p$ is a prime, $M$ a natural number with $5 \le M$ and $p \nmid M$, and $Pl$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`.
--
--   **Base data.** $L$ is a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, with $\zeta \in L$ a primitive $p$-th root of unity; $K$ is an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ subject to `hK`, which identifies $K$ with [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. with the subfield of $\mathrm{LaurentSeries}\,L$ generated over $L$ by the coefficientwise image of the $q$-expansion function field of $X_1(Mp)$ over $\mathbb{Q}$. $A$ is a discrete valuation domain with fraction field $L$ such that $p$ lies in its maximal ideal (`hAp`) and $\zeta$ lies in the image of $A$ (`hζA`), together with an $A$-algebra structure on $K$ making $A \to L \to K$ a scalar tower, and $j \in K$ is an element whose Laurent expansion is the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) (`hj`), assumed nonzero. The relevant curve over $A$ is the two-chart model [`ModularCurve.TwoChartModel A K j`](def/ModularCurve_TwoChartModel.html#L229), the pushout of the two affine charts $\operatorname{Spec}$ of the integral closures `chartAlgFin`, `chartAlgInf` along the middle chart, with structural morphism [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) to $\operatorname{Spec} A$, assumed proper.
--
--   **Residue field and special fibre.** The residue field $\kappa$ of $Pl$ is assumed algebraically closed of characteristic $p$ and an $A$-algebra. Two schemes $C_1, C_2$ with proper, smooth of relative dimension $1$, geometrically integral structural morphisms $c_1, c_2$ to $\operatorname{Spec}\kappa$ are given, together with closed immersions $i_1, i_2$ of them over $\kappa$ into the base change of the two-chart model to $\kappa$; `hcover` says every point of that base change lies in the image of $i_1$ or of $i_2$, `hred` says the fibre product of $i_1$ and $i_2$ (the intersection of the two components) is reduced, and `hn`, `hn0` say its cardinality is $n > 0$.
--
--   **Sections.** $\varepsilon$ is a section of `modelTo` over $\operatorname{Spec} A$, $\varepsilon_1, \varepsilon_2$ are sections of $c_1, c_2$, and `hε₁` says $\varepsilon_1$ followed by $i_1$ is the base change of $\varepsilon$ to $\kappa$.
--
--   **Relative Picard data.** $D$ is a `RelativePic0Designation` for `modelTo` (a scheme with a morphism `D.toBase` to $\operatorname{Spec} A$ and a zero section), `hrep` asserts that it represents the relative sub-Picard functor cut out by `algEquivZeroCut` (rigidified line bundles that are fibrewise algebraically equivalent to zero), and `hsm`, `hsep` assert that `D.toBase` is smooth and separated. `hreps` is such a representing datum after base change to $\kappa$, `hPk` compares its Poincaré bundle with the base change of the Poincaré bundle of `hrep.some`, and $D_1, D_2$ with `hrep₁`, `hrep₂` are representing data for $c_1, \varepsilon_1$ and $c_2, \varepsilon_2$. The morphism $\nu_2$ over $\kappa$ goes from the base of $D$ base-changed to $\kappa$ to that of $D_2$, and `hν₂` requires, for every $\kappa$-scheme point $a$, an isomorphism between the pullback of the $D_2$-Poincaré bundle along $a$ followed by $\nu_2$ and the rigidification along $\varepsilon_2$ of the pullback of the $D$-Poincaré bundle along $a$ through `curveChange i₂`.
--
--   **Fibres over $L$ and over $\overline{\mathbb{Q}}$.** Algebra structures making $A \to L \to \overline{\mathbb{Q}}$ a tower are assumed; `hsmL`, `hgiL` state that the base change of the two-chart model to $L$ is smooth of relative dimension $1$ and geometrically integral, and `hprL`, `hgcL` that the second projection of $D$ base-changed to $L$ is proper and geometrically connected. $M_\eta$ is a `CurveModel` over $\overline{\mathbb{Q}}$ for `x1FunctionFieldBar (M * p)`, $e_\eta$ an isomorphism of its underlying scheme with the $\overline{\mathbb{Q}}$-fibre of the two-chart model, compatible with the structural morphisms (`heη`), the finite chart of that fibre is nonempty, and `hMηpin` pins the identification on $q$-expansions: for every element $a$ of the finite chart algebra, the corresponding element of the function field has Laurent expansion the coefficientwise image under $L \to \overline{\mathbb{Q}}$ of the expansion of $a$. `hgal` is the Galois dictionary: for $g \in \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ trivial on $L$ and $\overline{\mathbb{Q}}$-points $x, x'$ of $M_\eta$ with $x'$ obtained from $x$ by precomposition with $\operatorname{Spec} g$ on the finite chart, the place attached to $x'$ is the image of the place attached to $x$ under [`ModularCurve.arithmeticGalois`](def/ModularCurve_ArithmeticGalois.html#L54) applied to $g$.
--
--   **Hecke, diamond and Galois actions.** `hin` and `hcomm` are the Hecke and diamond input conditions `HeckeDiamondInputsAll (M * p)` and `HeckeDiamondCommuteBar (M * p)`. A semiring action of $\operatorname{Gal}(L/\mathbb{Q})$ on $A$ is assumed, compatible with $A \to L$ (`hΓA`). The bijection `gpts` identifies $J_1(Mp) = \mathrm{Pic}^0$ of `x1FunctionFieldBar (M * p)` with the $\overline{\mathbb{Q}}$-points of $D$; the family $\varphi$ assigns to each element of the Hecke algebra `HeckeAlgOne` an endomorphism of `D.toBase` over $\operatorname{Spec} A$, and $\tau$ assigns to each $s \in \operatorname{Gal}(L/\mathbb{Q})$ a semilinear endomorphism of `D.toBase` over $\operatorname{Spec}$ of the action of $s$ on $A$. The hypotheses `hφmul`, `hφpts`, `hτ1`, `hτmul`, `hτφ`, `hgadd`, `hτpts` require: each $\varphi(t)$ is additive for the relative group law of `hrep.some`; `gpts` intertwines the Hecke module structure `heckeModuleOneBar (M * p)` with postcomposition by $\varphi(t)$; $\tau(1)$ is the identity and $\tau$ is multiplicative in diagrammatic order; each $\tau(s)$ commutes with each $\varphi(t)$; `gpts` is additive; and `gpts` is Galois-equivariant in the sense that for $\sigma' \in \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ inducing $s$ on $L$, the point attached to $\sigma' \cdot x$ is $\operatorname{Spec}\sigma'$ followed by the point attached to $x$ followed by $\tau(s^{-1})$.
--
--   **Abel–Jacobi data.** `hDL` is a representing datum after base change to $L$; $a_{jL}$ is a morphism over the $L$-fibre to the base of $D$ base-changed to $L$; $k_L$ compares the $\overline{\mathbb{Q}}$- and $L$-fibres (`hkL₁`, `hkL₂`); `hPL` compares Poincaré bundles over $L$; `hajLε` says $a_{jL}$ carries the cusp section to the zero section; `hajL` characterises $a_{jL}$ by the usual divisor recipe, namely for every field $K'$ over $L$ and every point $x$, the pullback of the Poincaré bundle along $x$ followed by $a_{jL}$ is the line bundle of the divisor of $x$ tensored with the ideal module of the divisor of the cusp. The morphism $a_{j\mathrm{bar}}$ is defined by `hajbar` as $e_\eta$, $k_L$, $a_{jL}$ and the first projection composed, lies over $\operatorname{Spec} A \to \operatorname{Spec}\overline{\mathbb{Q}}$ (`hajbar_over`), $\bar\varepsilon$ is a $\overline{\mathbb{Q}}$-point of $M_\eta$ over the cusp (`hεbar`) mapping to the zero section (`hεbar_aj`), and `hpts_aj` says that for $\overline{\mathbb{Q}}$-points $x$ and $s$ of $M_\eta$ with $s$ the cusp there is a degree-zero divisor equal to the difference of the places of $x$ and $s$ whose class under `gpts` is $x$ followed by $a_{j\mathrm{bar}}$.
--
--   **Special fibre group data.** $G$ is a `NeronSpecialFibreGeom p`, that is abelian groups `J0s`, `JI`, `JE`, a subgroup `torus` of `J0s` and a surjection `proj : J0s → JI × JE` with kernel `torus`. The bijections `pts`, `ptsI`, `ptsE` identify these groups with the $\kappa$-points of the bases of $D$ base-changed to $\kappa$, of $D_1$ and of $D_2$; `hadd`, `haddI`, `haddE` say that the corresponding Poincaré pullbacks are multiplicative (a tensor isomorphism for each sum); `hproj` says that `proj` is computed on $\kappa$-points by postcomposition with `RepresentsRelSubPic.pullbackHom` along $i_1$ in the first coordinate and with $\nu_2$ in the second; `hPTS` says `pts` is additive and sends $0$ to the identity. $O$ is a `NeronSpecialFibreOpsV3 G` (Hecke, diamond, Atkin–Lehner, inertia and further operators on these groups with their stated commutation relations), and `hO` is a fourfold hypothesis matching them with the morphisms above on $\kappa$-points: `O.hecke ℓ` with $\varphi(\mathrm{heckeGenOne}\,\ell)$ for every prime $\ell$; `O.diamondP b` with $\varphi(\mathrm{diamondGen} \,d)$ for every $d$ prime to $Mp$ with $d \equiv 1 \pmod M$ and $d \equiv b \pmod p$; `O.diamondN d` with $\varphi(\mathrm{diamondGen}\,d)$ for $d$ prime to $Mp$ with $d \equiv 1 \pmod p$; and `O.inertia b` with $\tau(s)$ for every $s \in \operatorname{Gal}(L/\mathbb{Q})$ with $s\zeta = \zeta^{b}$.
--
--   **Local data at $Pl$ and integral points.** `hPl` says $p$ is a nonunit of $Pl$; $\rho : A \to Pl$ satisfies `hρ` and `hAlgκ` (it lifts $A \to \overline{\mathbb{Q}}$ and induces $A \to \kappa$). The hypothesis `hF3` provides, for every subgroup $I$ of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ contained in the inertia subgroup of $Pl$ over $\mathbb{Q}$, fixing all $p$-th roots of unity, and of finite index in that inertia subgroup, a lift $\rho_I : A \to \mathcal{O}_I := Pl \cap \overline{\mathbb{Q}}^{\,I}$ of $A \to \overline{\mathbb{Q}}$ together with five clauses about the set $\mathrm{dom}$ of classes whose $\overline{\mathbb{Q}}$-point factors through $\operatorname{Spec}\mathcal{O}_I$: $I$ fixes every element of $\mathrm{dom}$; an $\mathcal{O}_I$-point is determined by its $\overline{\mathbb{Q}}$-point; $\mathrm{dom}$ contains $0$ and is closed under differences; for every $n > 0$ prime to $p$ the reduction map is injective on $n$-torsion $\mathcal{O}_I$-points and every $n$-torsion $\kappa$-point lifts to an $n$-torsion $\mathcal{O}_I$-point; and $\mathrm{dom}$ is stable under any $\varphi'$ which is a Frobenius at $Pl$ for $p$ and normalises $I$. The hypothesis `h𝒜` concerns a scheme $\mathcal{A}$ over $\operatorname{Spec} A$ with a closed immersion $\iota$ into $D$ over $A$, and has six clauses: $\iota$ is a closed immersion; $\mathcal{A} \to \operatorname{Spec} A$ is proper and smooth with connected geometric fibres; the image of $\iota$ is closed under the identity, multiplication and inversion of the relative group law; the classes in `normFreePartAt (M * p) p` are exactly those whose $\overline{\mathbb{Q}}$-point factors through $\mathcal{A}$; and the image of $\iota$ is stable under every $\varphi(t)$. The hypothesis `hF10` states that for every $\kappa$-algebra $T'$ and every $T'$-point $v$ of the base of $D$ base-changed to $\kappa$ that lifts to $\mathcal{A}$, the composite of $v$ with $\varphi$ of $\sum_{b \in (\mathbb{Z}/p)^\times} \mathrm{diamondGen}$ of the Chinese-remainder lift of $(b, 1)$ is the identity element.
--
--   **Igusa components and gluing data.** $w$ is an `IntegralWeightOneForm` over $\kappa$ of level $M$, and $\mathrm{Mdl}_1, \mathrm{Mdl}_2$ are curve models over $\kappa$ for the Igusa function field `igusaFunctionFieldX1C κ M w`, with isomorphisms $e_1, e_2$ onto $C_1, C_2$ compatible with the structural morphisms (`he₁`, `he₂`). The finite chart of $C_1$ is nonempty, and `hgauss₁` is the $q$-expansion reading on $C_1$: for every element $a$ of the finite chart algebra and power series $x, y$ over $A$ with $y$ having nonzero reduction and $a \cdot y = x$ in $\mathrm{LaurentSeries}\,L$, the element of the Igusa function field determined by $a$ through $e_1$, $i_1$ and the first projection has Laurent expansion the quotient of the reductions of $x$ and $y$. Further, `hεC₂` says the reduction of the cusp section avoids the image of $i_2$, and `hεgal` says $\varepsilon$ is equivariant for every automorphism of the two-chart model lying over the action of $s \in \operatorname{Gal}(L/\mathbb{Q})$ on $A$ and induced on the finite chart algebra by a coefficientwise ring automorphism. Finally `nodesIg` is a finite set of pairs of places of the Igusa function field, $\Psi$ an isomorphism of `G.J0s` with `GluedPic0 κ F nodesIg` (classes of admissible gluing data: pairs of degree-zero divisors vanishing at the nodes together with units at the nodes, modulo glued principal data), and $\theta_1, \theta_2$ isomorphisms of `G.JI`, `G.JE` with $\mathrm{Pic}^0$ of that field. The hypothesis `hF4c` has seven clauses: `nodesIg` consists exactly of the pairs of places cut out by the $\kappa$-points of the intersection of the two components; its cardinality is $n$; both projections are injective on it; `GluedPic0.toPic0Pair` composed with $\Psi$ equals $(\theta_1, \theta_2)$ composed with `G.proj`; the image of `G.torus` under $\Psi$ is the range of `GluedPic0.nodeUnit`; and $\theta_1$, $\theta_2$ are computed by the expected divisor differences on $C_1$ and on $C_2$ whenever the Poincaré pullback is isomorphic to the line bundle of a point tensored with the ideal module of the respective cusp section. The automorphism `frobT` is an element of `SemilinearAut κ F` for the Igusa function field, that is a pair of ring automorphisms compatible with $\kappa \to F$, and `hfrobT` requires that it raise every Laurent coefficient to the $p$-th power.
--
--   **The specialisation family.** `dom𝒟` assigns to each admissible $I$ (with its three proofs) a subgroup of $J_1(Mp)$, and `sp𝒟` an additive map from that subgroup to `GluedPic0 κ F nodesIg`. The interface `hIFm` has two clauses: membership in `dom𝒟` holds precisely when the $\overline{\mathbb{Q}}$-point of the class factors through $\operatorname{Spec}\mathcal{O}_I$ via the lift supplied by `hF3`; and `sp𝒟` of such a class is $\Psi$ of the element of `G.J0s` corresponding under `pts` to the reduction of that $\mathcal{O}_I$-point to $\kappa$. The hypothesis `hlev` has two clauses: for $J \le I$ both admissible, an $\mathcal{O}_I$-point restricts to an $\mathcal{O}_J$-point with the same $\overline{\mathbb{Q}}$-point and the same reduction to $\kappa$; and `dom𝒟` and `sp𝒟` are compatible with shrinking $I$ to $J$.
--
--   **Conclusion.** For every subgroup $I$ of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ contained in the inertia subgroup of $Pl$ over $\mathbb{Q}$, fixing every $p$-th root of unity in $\overline{\mathbb{Q}}$, and of finite index in that inertia subgroup; for every automorphism $\varphi$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ which is a Frobenius at $Pl$ for $p$, in the sense that $\varphi$ lies in the decomposition subgroup of $Pl$ and acts on the residue field of $Pl$ by $x \mapsto x^p$ (in the conclusion the binder $\varphi$ shadows the family of Hecke endomorphisms named $\varphi$ above); and for every $y$ in `dom𝒟 I …` such that $\varphi \cdot y$, the Galois translate of the underlying class in $\mathrm{Pic}^0$ of `laurentBaseChange (AlgebraicClosure ℚ) (x1FunctionField (M * p))`, again lies in `dom𝒟 I …`: the first component of `GluedPic0.toPic0Pair nodesIg` applied to `sp𝒟 I …` of $\varphi \cdot y$ equals `frobT` applied to the first component of `GluedPic0.toPic0Pair nodesIg` applied to `sp𝒟 I …` of $y$.
--
--   Thus, on the Igusa component carrying the cusp the specialisation map is equivariant for Frobenius, the action on $\mathrm{Pic}^0$ of the Igusa function field being the one induced by the coefficientwise $p$-th power automorphism.
--
--   This is the Frobenius clause of the specialisation package for the norm-free part of $J_1(Mp)$ at $p$: it records that, after reduction to the special fibre of the semistable model of $X_1(Mp)$ at $p$ and Raynaud's description of $\mathrm{Pic}^0$ of the two glued Igusa components, a Frobenius element at the chosen place acts on the component through the cusp by the coefficientwise $p$-th power map on $q$-expansions. It is used in the assembly of the pinned $q$-expansion specialisation datum with diamond operators for $J_1(Mp)$, which feeds the level-lowering step at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_normFreePartFamily_toPic0Pair_sp_fst_smul_of_isFrobeniusAt_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV3
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_QExpSemistableSpecializationPinned
import Definitions.Def_ModularCurve_QExpSemistableSpecializationPinnedV3
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
import Definitions.Def_ValuationSubring_ReduceAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open ModularCurve IntermediateField

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.XOneP.normFreePartFamily_toPic0Pair_sp_fst_smul_of_isFrobeniusAt_twoChartModel_x1_mul
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)] [CharP (IsLocalRing.ResidueField ↥Pl) p] [Algebra A (IsLocalRing.ResidueField ↥Pl)]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl))) (c₂ : C₂ ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (IsLocalRing.ResidueField ↥Pl))) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (IsLocalRing.ResidueField ↥Pl)))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (IsLocalRing.ResidueField ↥Pl))), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange (IsLocalRing.ResidueField ↥Pl) ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (IsLocalRing.ResidueField ↥Pl)) (sectionBaseChange (IsLocalRing.ResidueField ↥Pl) ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (IsLocalRing.ResidueField ↥Pl)) (sectionBaseChange (IsLocalRing.ResidueField ↥Pl) ε)) (D.baseChange (IsLocalRing.ResidueField ↥Pl)))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε (IsLocalRing.ResidueField ↥Pl)
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)), pullback.condition⟩)).L))
    (D₁ : RelativePic0Designation (IsLocalRing.ResidueField ↥Pl) c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation (IsLocalRing.ResidueField ↥Pl) c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl))) (a : SchemeHomOver t (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (hsmL : SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))
    (hgiL : GeometricallyIntegral (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))

    (hprL : IsProper (pullback.snd D.toBase (specMap A L)))
    (hgcL : GeometricallyConnected (pullback.snd D.toBase (specMap A L)))

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)

    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hMηpin : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      ((Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L))

    (hgal : ∀ (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)),
      (∀ l : L, g (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      Mη.pointEquivPlace x' =
        ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField (M * p)) g • Mη.pointEquivPlace x)
    (hin : ModularCurve.HeckeDiamondInputsAll (M * p)) (hcomm : ModularCurve.HeckeDiamondCommuteBar (M * p))

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

    (G : ModularCurve.JOneP.NeronSpecialFibreGeom p)
    (pts : G.J0s ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase)
    (ptsI : G.JI ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) D₁.toBase)
    (ptsE : G.JE ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) D₂.toBase)
    (hadd : ∀ a b : G.J0s, Nonempty
      ((hreps.poincare.pullbackAlong (pts (a + b))).L ≅
        (hreps.poincare.pullbackAlong (pts a)).L ⊗ (hreps.poincare.pullbackAlong (pts b)).L))
    (haddI : ∀ a b : G.JI, Nonempty
      ((hrep₁.some.poincare.pullbackAlong (ptsI (a + b))).L ≅
        (hrep₁.some.poincare.pullbackAlong (ptsI a)).L ⊗ (hrep₁.some.poincare.pullbackAlong (ptsI b)).L))
    (haddE : ∀ a b : G.JE, Nonempty
      ((hrep₂.some.poincare.pullbackAlong (ptsE (a + b))).L ≅
        (hrep₂.some.poincare.pullbackAlong (ptsE a)).L ⊗ (hrep₂.some.poincare.pullbackAlong (ptsE b)).L))
    (hproj : ∀ x : G.J0s,
      ptsI (G.proj x).1 =
        postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) (pts x) ∧
      ptsE (G.proj x).2 = postComp ν₂ (pts x))

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (φ : ModularCurve.HeckeAlgOne → SchemeHomOver D.toBase D.toBase)
    (τ : ∀ s : L ≃ₐ[ℚ] L,
      SchemeHomOver (D.toBase ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))) D.toBase)
    (hφmul : ∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s x y) (φ t) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
          (NeronModelInfra.schemeHomOverComp x (φ t)) (NeronModelInfra.schemeHomOverComp y (φ t)))
    (hφpts : letI := ModularCurve.heckeModuleOneBar (M * p)
      ∀ (t : ModularCurve.HeckeAlgOne) (x : ModularCurve.JOne (M * p)), (gpts (t • x)).1 = (gpts x).1 ≫ (φ t).1)
    (hτ1 : (τ 1).1 = 𝟙 D.P) (hτmul : ∀ s s' : L ≃ₐ[ℚ] L, (τ (s * s')).1 = (τ s).1 ≫ (τ s').1)
    (hτφ : ∀ (t : ModularCurve.HeckeAlgOne) (s : L ≃ₐ[ℚ] L), (τ s).1 ≫ (φ t).1 = (φ t).1 ≫ (τ s).1)

    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))
    (hτpts : ∀ (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (s : L ≃ₐ[ℚ] L),
      (∀ l : L, σ' (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) (s l)) →
      ∀ x : ModularCurve.JOne (M * p),
        (gpts (σ' • x)).1 = Spec.map (CommRingCat.ofHom σ'.toRingEquiv.toRingHom) ≫ (gpts x).1 ≫ (τ s⁻¹).1)

    (hDL : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)
        (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)) (D.baseChange L))
    (ajL : SchemeHomOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (D.baseChange L).toBase)
    (kL : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L))
    (ajbar : Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hPL : Nonempty (hDL.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε L
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A L), pullback.condition⟩)).L))
    (hajLε : (sectionBaseChange L ε).1 ≫ ajL.1 = (D.baseChange L).zeroSection)
    (hajL : (∀ (K' : Type) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of L))
        (x : SchemeHomOver t (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L)),
      Nonempty ((hDL.poincare.pullbackAlong
          ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (t ≫ (sectionBaseChange L ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange L ε).2).trans
              (Category.comp_id t)))).idealModule)))
    (hkL₁ : kL ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
    (hkL₂ : kL ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ≫ specMap L (AlgebraicClosure ℚ))
    (hajbar : ajbar = eη ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap A L))
    (hajbar_over : ajbar ≫ D.toBase = Mη.toBase ≫ specMap A (AlgebraicClosure ℚ))
    (hεbar : εbar.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1)
    (hεbar_aj : εbar.1 ≫ ajbar = specMap A (AlgebraicClosure ℚ) ≫ D.zeroSection)
    (hpts_aj : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (gpts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))
    (O : ModularCurve.JOneP.NeronSpecialFibreOpsV3 G)
    (hO :
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (y : G.J0s),
        (pts (O.hecke ℓ y)).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) =
          ((pts y).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl))) ≫ (φ (ModularCurve.heckeGenOne ⟨ℓ, hℓ⟩)).1) ∧
      (∀ (b : (ZMod p)ˣ) (d : ℕ), d.Coprime (M * p) → (d : ZMod M) = 1 → (d : ZMod p) = (b : ZMod p) →
        ∀ y : G.J0s,
          (pts (O.diamondP b y)).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) =
            ((pts y).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl))) ≫ (φ (ModularCurve.diamondGen d)).1) ∧
      (∀ d : ℕ, d.Coprime (M * p) → (d : ZMod p) = 1 → ∀ y : G.J0s,
        (pts (O.diamondN d y)).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) =
          ((pts y).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl))) ≫ (φ (ModularCurve.diamondGen d)).1) ∧

      (∀ (b : (ZMod p)ˣ) (s : L ≃ₐ[ℚ] L), s ζ = ζ ^ (b : ZMod p).val → ∀ y : G.J0s,
        (pts (O.inertia b y)).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) =
          ((pts y).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl))) ≫ (τ s).1) )
    (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (hAlgκ : algebraMap A (IsLocalRing.ResidueField ↥Pl) = (IsLocalRing.residue ↥Pl).comp ρ)
    (hF3 : ∀
    (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ)
    (hIμ : ∀ σ ∈ I, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ')
    (hIf : (I.subgroupOf (Pl.inertiaSubgroupIn ℚ)).FiniteIndex),

    let OI : Subring (AlgebraicClosure ℚ) := Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring
    ∃ (ρI : A →+* ↥OI) (hρI : OI.subtype.comp ρI = algebraMap A (AlgebraicClosure ℚ)),

      let toκ : ↥OI →+* IsLocalRing.ResidueField ↥Pl := (IsLocalRing.residue ↥Pl).comp (Subring.inclusion inf_le_left)

      let DOI := SchemeHomOver (Spec.map (CommRingCat.ofHom ρI)) D.toBase
      let Dκ := SchemeHomOver (Spec.map (CommRingCat.ofHom (toκ.comp ρI))) D.toBase

      let dom : Set (ModularCurve.JOne (M * p)) :=
        {x | ∃ z : DOI, (gpts x).1 = Spec.map (CommRingCat.ofHom OI.subtype) ≫ z.1}

      (∀ x ∈ dom, ∀ σ ∈ I, σ • x = x) ∧

      (∀ z z' : DOI, Spec.map (CommRingCat.ofHom OI.subtype) ≫ z.1 = Spec.map (CommRingCat.ofHom OI.subtype) ≫ z'.1 → z = z') ∧

      (0 ∈ dom ∧ ∀ x ∈ dom, ∀ y ∈ dom, x - y ∈ dom) ∧

      (letI := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).pointGroup
          (Spec.map (CommRingCat.ofHom ρI))
       letI := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).pointGroup
          (Spec.map (CommRingCat.ofHom (toκ.comp ρI)))
       ∀ n : ℕ, 0 < n → ¬ p ∣ n →
         (∀ z : DOI, z ^ n = 1 → Spec.map (CommRingCat.ofHom toκ) ≫ z.1 = (1 : Dκ).1 → z = 1) ∧
         (∀ w : Dκ, w ^ n = 1 → ∃ z : DOI, z ^ n = 1 ∧ w.1 = Spec.map (CommRingCat.ofHom toκ) ≫ z.1)) ∧

      (∀ φ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, Pl.IsFrobeniusAt φ' p →
        (∀ σ, σ ∈ I ↔ φ' * σ * φ'⁻¹ ∈ I) → ∀ x ∈ dom, φ' • x ∈ dom))
    (𝒜 : Scheme.{0}) (a : 𝒜 ⟶ Spec (CommRingCat.of A)) (ι : SchemeHomOver a D.toBase)
    (h𝒜 :

      IsClosedImmersion ι.1 ∧

      IsProper a ∧ Smooth a ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
        ConnectedSpace ↥(pullback a s)) ∧

      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)),
        (∃ o : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp o ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).one s) ∧
        (∀ x y : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
            (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι)) ∧
        (∀ x : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).inv s
            (NeronModelInfra.schemeHomOverComp x ι))) ∧

      (∀ x : ModularCurve.JOne (M * p),
        x ∈ ModularCurve.normFreePartAt (M * p) p ↔
          ∃ y : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) a, y.1 ≫ ι.1 = (gpts x).1) ∧

      (∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x : SchemeHomOver s a),
        ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x ι) (φ t)))
    (hF10 :
    ∀ (T' : Type) [CommRing T'] [Algebra (IsLocalRing.ResidueField ↥Pl) T']
      (v : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField ↥Pl) T'))) (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase),
      (∃ z : Spec (CommRingCat.of T') ⟶ 𝒜,
          z ≫ a = Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField ↥Pl) T')) ≫ specMap A (IsLocalRing.ResidueField ↥Pl) ∧
          v.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) = z ≫ ι.1) →
      (v.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl))) ≫
          (φ (∑ b : (ZMod p)ˣ, ModularCurve.diamondGen
            ((ZMod.chineseRemainder ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hpM)).symm ((b : ZMod p), 1)).val)).1 =
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).one
          (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField ↥Pl) T')) ≫ specMap A (IsLocalRing.ResidueField ↥Pl))).1)

    (w : ModularCurve.IntegralWeightOneForm (IsLocalRing.ResidueField ↥Pl) M)
    (Mdl₁ : AlgebraicCurve.CurveModel (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    (Mdl₂ : AlgebraicCurve.CurveModel (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) (e₂ : Mdl₂.C ≅ C₂)
    (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

    [hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (IsLocalRing.ResidueField ↥Pl))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hgauss₁ : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A (IsLocalRing.ResidueField ↥Pl)) ≠ 0 →
      ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      ((Mdl₁.ffEquiv.symm
          (Mdl₁.C.germToFunctionField ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (IsLocalRing.ResidueField ↥Pl))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (IsLocalRing.ResidueField ↥Pl))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField ↥Pl) (x.map (algebraMap A (IsLocalRing.ResidueField ↥Pl))) / HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField ↥Pl) (y.map (algebraMap A (IsLocalRing.ResidueField ↥Pl))))

    (hεC₂ : ∀ t, ((sectionBaseChange (IsLocalRing.ResidueField ↥Pl) ε).1).base t ∉ Set.range i₂.1.base)
    (hεgal : ∀ (s : L ≃ₐ[ℚ] L) (ws : ModularCurve.TwoChartModel A (↥K) j ⟶ ModularCurve.TwoChartModel A (↥K) j),
      ws ≫ ModularCurve.TwoChart.modelTo A (↥K) j =
        ModularCurve.TwoChart.modelTo A (↥K) j ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)) →
      ∀ (ρs : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)),
      (∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        (((ρs b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) =
          ModularCurve.coeffMap (s.toAlgHom.toRingHom) (((b : ↥K)) : LaurentSeries L)) →
      ModularCurve.TwoChart.ιFin A (↥K) j ≫ ws = Spec.map (CommRingCat.ofHom ρs.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j →
      ε.1 ≫ ws = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)) ≫ ε.1)
    (hPTS :
    (∀ a b : G.J0s, pts (a + b) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps).mul _ (pts a) (pts b)) ∧
    pts 0 = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps).one _)
    (nodesIg : Finset (AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) × AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)))
    (Ψ : G.J0s ≃+ AlgebraicCurve.GluedPic0 (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) nodesIg)
    (θ₁ : G.JI ≃+ AlgebraicCurve.Pic0 (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w))
    (θ₂ : G.JE ≃+ AlgebraicCurve.Pic0 (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w))
    (hF4c :

      (∀ σ : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) × AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w),
        σ ∈ nodesIg ↔ ∃ (z : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)) ⟶ pullback i₁.1 i₂.1)
          (hz₁ : (z ≫ pullback.fst i₁.1 i₂.1) ≫ c₁ = 𝟙 _) (hz₂ : (z ≫ pullback.snd i₁.1 i₂.1) ≫ c₂ = 𝟙 _),
          σ.1 = Mdl₁.pointEquivPlace ⟨(z ≫ pullback.fst i₁.1 i₂.1) ≫ e₁.inv,
            by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact hz₁⟩ ∧
          σ.2 = Mdl₂.pointEquivPlace ⟨(z ≫ pullback.snd i₁.1 i₂.1) ≫ e₂.inv,
            by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact hz₂⟩) ∧
      nodesIg.card = n ∧
      Set.InjOn Prod.fst (nodesIg : Set (AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) × AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w))) ∧
      Set.InjOn Prod.snd (nodesIg : Set (AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) × AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w))) ∧

      (∀ x : G.J0s, AlgebraicCurve.GluedPic0.toPic0Pair nodesIg (Ψ x) = (θ₁ (G.proj x).1, θ₂ (G.proj x).2)) ∧

      (G.torus.map Ψ.toAddMonoidHom = (AlgebraicCurve.GluedPic0.nodeUnit nodesIg).range) ∧

      (∀ (g : G.JI) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) c₁),
        Nonempty ((hrep₁.some.poincare.pullbackAlong (ptsI g)).L ≅
          (RelEffCartierDiv.ofPoint c₁ x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₁ ε₁.1 ε₁.2).idealModule) →
        ∃ Dv : Divisor.degZero (K := (IsLocalRing.ResidueField ↥Pl)) (F := ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)),
          (Dv : Divisor (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) =
            Finsupp.single (Mdl₁.pointEquivPlace ⟨x.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact x.2⟩) 1 -
              Finsupp.single (Mdl₁.pointEquivPlace ⟨ε₁.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact ε₁.2⟩) 1 ∧
          θ₁ g = Pic0.mk Dv) ∧

      (∀ (g : G.JE) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) c₂),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (ptsE g)).L ≅
          (RelEffCartierDiv.ofPoint c₂ x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₂ ε₂.1 ε₂.2).idealModule) →
        ∃ Dv : Divisor.degZero (K := (IsLocalRing.ResidueField ↥Pl)) (F := ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)),
          (Dv : Divisor (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) =
            Finsupp.single (Mdl₂.pointEquivPlace ⟨x.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact x.2⟩) 1 -
              Finsupp.single (Mdl₂.pointEquivPlace ⟨ε₂.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact ε₂.2⟩) 1 ∧
          θ₂ g = Pic0.mk Dv))
    (frobT : SemilinearAut (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w))
    (hfrobT : ∀ (x : ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) (n : ℤ),
      ((frobT • x : ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)).coeff n = ((x : LaurentSeries (IsLocalRing.ResidueField ↥Pl)).coeff n) ^ p)
    (dom𝒟 : ∀ (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ)
      (hIμ : ∀ σ ∈ I, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ') (hIf : (I.subgroupOf (Pl.inertiaSubgroupIn ℚ)).FiniteIndex), AddSubgroup (ModularCurve.JOne (M * p)))
    (sp𝒟 : ∀ (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ)
      (hIμ : ∀ σ ∈ I, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ') (hIf : (I.subgroupOf (Pl.inertiaSubgroupIn ℚ)).FiniteIndex),
      ↥(dom𝒟 I hI hIμ hIf) →+ AlgebraicCurve.GluedPic0 (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) nodesIg)
    (hIFm : ∀ (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ)
      (hIμ : ∀ σ ∈ I, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ') (hIf : (I.subgroupOf (Pl.inertiaSubgroupIn ℚ)).FiniteIndex),
      (∀ y : ModularCurve.JOne (M * p), y ∈ dom𝒟 I hI hIμ hIf ↔ ∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase,
          (gpts y).1 = Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype) ≫ z.1) ∧
      (∀ (y : ModularCurve.JOne (M * p)) (hy : y ∈ dom𝒟 I hI hIμ hIf) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase)
        (hz : (gpts y).1 = Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype) ≫ z.1) (u : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase),
        u.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring) ≤ Pl.toSubring)))) ≫ z.1 →
        sp𝒟 I hI hIμ hIf ⟨y, hy⟩ = Ψ (pts.symm u)))
    (hlev : (∀ (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ)
      (hIμ : ∀ σ ∈ I, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ') (hIf : (I.subgroupOf (Pl.inertiaSubgroupIn ℚ)).FiniteIndex)
      (J : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hJ : J ≤ Pl.inertiaSubgroupIn ℚ)
      (hJμ : ∀ σ ∈ J, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ') (hJf : (J.subgroupOf (Pl.inertiaSubgroupIn ℚ)).FiniteIndex) (hle : J ≤ I) (y : ModularCurve.JOne (M * p))
      (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase)
      (hz : (gpts y).1 = Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype) ≫ z.1),
      ∃ (hOO : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring) ≤ (Pl.toSubring ⊓ (IntermediateField.fixedField J).toSubring))
        (zJ : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 J hJ hJμ hJf)))) D.toBase),
        zJ.1 = Spec.map (CommRingCat.ofHom (Subring.inclusion hOO)) ≫ z.1 ∧
        (gpts y).1 = Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField J).toSubring).subtype) ≫ zJ.1 ∧
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left : (Pl.toSubring ⊓ (IntermediateField.fixedField J).toSubring) ≤ Pl.toSubring)))) ≫ zJ.1 = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring) ≤ Pl.toSubring)))) ≫ z.1) ∧
    (∀ (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ)
      (hIμ : ∀ σ ∈ I, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ') (hIf : (I.subgroupOf (Pl.inertiaSubgroupIn ℚ)).FiniteIndex)
      (J : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hJ : J ≤ Pl.inertiaSubgroupIn ℚ)
      (hJμ : ∀ σ ∈ J, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ') (hJf : (J.subgroupOf (Pl.inertiaSubgroupIn ℚ)).FiniteIndex) (hle : J ≤ I) (y : ModularCurve.JOne (M * p))
      (hy : y ∈ dom𝒟 I hI hIμ hIf), ∃ hyJ : y ∈ dom𝒟 J hJ hJμ hJf, sp𝒟 J hJ hJμ hJf ⟨y, hyJ⟩ = sp𝒟 I hI hIμ hIf ⟨y, hy⟩))
    :
      ∀ (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ)
      (hIμ : ∀ σ ∈ I, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ') (hIf : (I.subgroupOf (Pl.inertiaSubgroupIn ℚ)).FiniteIndex),
      ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          Pl.IsFrobeniusAt φ p → ∀ (y : (dom𝒟 I hI hIμ hIf))
            (h : φ • (y : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField (M * p)))) ∈ (dom𝒟 I hI hIμ hIf)),
            (GluedPic0.toPic0Pair nodesIg
                ((sp𝒟 I hI hIμ hIf) ⟨φ • (y : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField (M * p)))), h⟩)).1 =
              frobT • (GluedPic0.toPic0Pair nodesIg ((sp𝒟 I hI hIμ hIf) y)).1 := by sorry
