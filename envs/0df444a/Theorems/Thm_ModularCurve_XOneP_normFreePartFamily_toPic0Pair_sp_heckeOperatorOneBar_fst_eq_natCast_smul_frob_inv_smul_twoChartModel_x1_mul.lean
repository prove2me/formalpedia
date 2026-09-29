-- Prove2me | Theorems.Thm_ModularCurve_XOneP_normFreePartFamily_toPic0Pair_sp_heckeOperatorOneBar_fst_eq_natCast_smul_frob_inv_smul_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.normFreePartFamily_toPic0Pair_sp_heckeOperatorOneBar_fst_eq_natCast_smul_frob_inv_smul_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/3ab13dd4-44f1-5690-8092-3d492d35cc2f
-- title:
--   Uₚ acts as p Fr⁻¹ on norm-free specialisations
-- statement:
--   Fix a prime $p$, an integer $M$ with $5 \le M$ and $p \nmid M$, and a valuation subring $Pl$ of $\overline{\mathbb{Q}}$; write $\kappa$ for the residue field `IsLocalRing.ResidueField ↥Pl`, which is assumed algebraically closed of characteristic $p$ and an $A$-algebra for the ring $A$ below.
--
--   *Arithmetic data.* $L$ is a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and $\zeta \in L$ a primitive $p$-th root of unity. $K$ is an intermediate field of $L \subseteq \operatorname{LaurentSeries} L$ with `hK` identifying it with [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), the function field of $X_1(Mp)$ over $L$ realised by $q$-expansions. $A$ is a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal (`hAp`) and $\zeta$ in the image of $A$ (`hζA`), together with an $A$-algebra structure on $K$ compatible with $L$. The element $j \in K$ is nonzero and has Laurent expansion the $q$-expansion of the modular $j$-function (`hj`); [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) is the resulting two-chart model of $X_1(Mp)$ over $\operatorname{Spec} A$, assumed proper, and its generic and special fibres are described by the further hypotheses.
--
--   *The two components of the special fibre.* $C_1, C_2$ are proper, smooth of relative dimension $1$, geometrically integral curves over $\kappa$, given as closed subschemes $i_1, i_2$ of the base change of the two-chart model to $\kappa$; `hcover` says their images cover that base change, `hred` that the scheme-theoretic intersection `pullback i₁.1 i₂.1` is reduced, and `hn`, `hn0` that its number of points is $n > 0$. Sections $\varepsilon$ of the model over $A$ and $\varepsilon_1, \varepsilon_2$ of $c_1, c_2$ are given, with `hε₁` asserting that $\varepsilon_1$ followed by $i_1$ is the base change of $\varepsilon$ to $\kappa$, and `hεC₂` that the reduction of $\varepsilon$ meets no point of the image of $i_2$.
--
--   *Relative Picard data.* $D$ is a `RelativePic0Designation` for the model over $A$ (a scheme `D.P` over $\operatorname{Spec} A$ with a zero section); `hrep` asserts that $D$ represents, relative to $\varepsilon$, the functor of rigidified line bundles satisfying the fibrewise algebraic-equivalence-to-zero condition `algEquivZeroCut`, and `hsm`, `hsep` that `D.toBase` is smooth and separated. The hypotheses `hreps`, `hPk` give the corresponding representability over $\kappa$ for `D.baseChange κ` together with an isomorphism of Poincaré bundles under base change; $D_1, D_2$ with `hrep₁`, `hrep₂` do the same for $c_1, c_2$. The morphism $\nu_2$ from `D.baseChange κ` to $D_2$ is pinned by `hν₂`, which says that for every $\kappa$-scheme point $a$ of `(D.baseChange κ).toBase` the Poincaré bundle of $D_2$ pulled back along $a$ followed by $\nu_2$ is isomorphic to the rigidification along $\varepsilon_2$ of the pullback of the Poincaré bundle of `D.baseChange κ` along the curve change given by $i_2$. Over $L$, `hsmL`, `hgiL`, `hprL`, `hgcL` assert smoothness of relative dimension one and geometric integrality of the base change of the model to $L$, and properness and geometric connectedness of `pullback.snd D.toBase (specMap A L)`.
--
--   *The geometric fibre and Galois action.* $A$ and $L$ are algebras in $\overline{\mathbb{Q}}$ with the evident scalar tower. $M_\eta$ is a `CurveModel` over $\overline{\mathbb{Q}}$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182), $e_\eta$ an isomorphism of its underlying scheme with the base change of the two-chart model to $\overline{\mathbb{Q}}$ compatible with the structure morphisms (`heη`); `hMηpin` reads the finite chart algebra of the model inside the function field of $M_\eta$ as the image under [`ModularCurve.coeffMap`](def/ModularCurve_LaurentCoeff.html#L16) of the Laurent expansions over $L$, and `hgal` states that any automorphism of $\overline{\mathbb{Q}}$ fixing $L$ pointwise transports the place attached to a $\overline{\mathbb{Q}}$-point of $M_\eta$ by the corresponding element [`ModularCurve.arithmeticGalois`](def/ModularCurve_ArithmeticGalois.html#L54) of the semilinear automorphism group. The hypotheses `hin` and `hcomm` are [`ModularCurve.HeckeDiamondInputsAll (M * p)`](def/ModularCurve_X1HeckeModule.html#L58) and [`ModularCurve.HeckeDiamondCommuteBar (M * p)`](def/ModularCurve_X1HeckeModule.html#L54), the inputs making the Hecke and diamond operators available and commuting on $J_1(Mp)(\overline{\mathbb{Q}}) =$ [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186). A semiring action of $\operatorname{Gal}(L/\mathbb{Q})$ on $A$ compatible with $A \to L$ is given (`hΓA`).
--
--   *Special fibre datum and dictionaries of points.* $G$ is a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9): abelian groups `G.J0s`, `G.JI`, `G.JE`, a subgroup `G.torus` of `G.J0s`, and a surjection `G.proj` onto `G.JI × G.JE` with kernel `G.torus`. The equivalences `pts`, `ptsI`, `ptsE` identify `G.J0s`, `G.JI`, `G.JE` with the $\kappa$-points of `(D.baseChange κ).toBase`, `D₁.toBase`, `D₂.toBase`; `hadd`, `haddI`, `haddE` express additivity of these dictionaries through tensor isomorphisms of the pulled-back Poincaré bundles, `hPTS` states that `pts` is additive for the relative group law and sends $0$ to the identity, and `hproj` identifies the two components of `G.proj` with composition with the comparison morphism `RepresentsRelSubPic.pullbackHom` attached to $i_1$ and with $\nu_2$ respectively.
--
--   *Operators on $D$.* `gpts` identifies [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186) with the $\overline{\mathbb{Q}}$-points of `D.toBase`; $\varphi$ assigns to each element of the Hecke algebra [`ModularCurve.HeckeAlgOne`](def/ModularCurve_X1HeckeModule.html#L16) an endomorphism of $D$ over $\operatorname{Spec} A$, and $\tau$ assigns to each $s \in \operatorname{Gal}(L/\mathbb{Q})$ a morphism of $D$ semilinear over the induced automorphism of $A$. The compatibilities are: `hφmul` ($\varphi t$ is a homomorphism for the relative group law), `hφpts` (`gpts` intertwines the Hecke module structure [`ModularCurve.heckeModuleOneBar`](def/ModularCurve_X1HeckeModule.html#L129) with the $\varphi t$), `hτ1`, `hτmul` ($\tau$ is multiplicative), `hτφ` ($\tau$ and $\varphi$ commute), `hgadd` (`gpts` is additive) and `hτpts` (`gpts` is equivariant for the Galois action, an automorphism of $\overline{\mathbb{Q}}$ restricting to $s$ on $L$ acting through $\tau(s^{-1})$).
--
--   *Abel–Jacobi data.* Over $L$: `hDL` is the representability statement for `D.baseChange L`, `ajL` a morphism from the base-changed curve to `(D.baseChange L).toBase` with `hajLε` sending the cusp section to the zero section and `hajL` characterising it by the isomorphism of the pulled-back Poincaré bundle with the line bundle of the point tensored with the ideal module of $\varepsilon$, and `hPL` compares Poincaré bundles under base change. The morphism `kL` between the geometric fibres is pinned by `hkL₁`, `hkL₂`; `ajbar` is the induced morphism from $M_\eta$ to `D.P` (`hajbar`, `hajbar_over`); $\bar\varepsilon$ is the $\overline{\mathbb{Q}}$-point of $M_\eta$ lying over $\varepsilon$ (`hεbar`) and mapping to the zero section (`hεbar_aj`); `hpts_aj` says that for $\overline{\mathbb{Q}}$-points $x$ and $s$ of $M_\eta$, with $s$ the cusp, there is a degree-zero divisor equal to the difference of the places of $x$ and of $s$ whose class under `gpts` is $x$ followed by `ajbar`.
--
--   *Operators on the special fibre.* $O$ is a [`ModularCurve.JOneP.NeronSpecialFibreOpsV3 G`](def/ModularCurve_JOnePOpsV3.html#L13), providing Hecke operators, diamond operators indexed by $(\mathbb{Z}/p)^\times$ and by integers, an involution, inertia operators and Verschiebung/Frobenius on the components, with their mutual commutations. The four clauses of `hO` match these with the operators on $D$ under `pts`: `O.hecke ℓ` with $\varphi(\mathtt{heckeGenOne}\ \ell)$ for every prime $\ell$; `O.diamondP b` with $\varphi(\mathtt{diamondGen}\ d)$ whenever $d$ is coprime to $Mp$, $d \equiv 1 \bmod M$ and $d \equiv b \bmod p$; `O.diamondN d` with $\varphi(\mathtt{diamondGen}\ d)$ whenever $d$ is coprime to $Mp$ and $d \equiv 1 \bmod p$; and `O.inertia b` with $\tau(s)$ whenever $s \in \operatorname{Gal}(L/\mathbb{Q})$ sends $\zeta$ to $\zeta^{b}$.
--
--   *Integral points over inertia-fixed subrings.* `hPl` says $p$ lies in the non-units of $Pl$, and $\rho$, `hρ`, `hAlgκ` give a lift of $A \to \overline{\mathbb{Q}}$ through $Pl$ compatible with the map to $\kappa$. The hypothesis `hF3` concerns an arbitrary subgroup $I$ of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ contained in the inertia subgroup of $Pl$ over $\mathbb{Q}$, acting trivially on the $p$-th roots of unity, and of finite index in that inertia subgroup; with $\mathcal{O}_I = Pl \cap \overline{\mathbb{Q}}^{\,I}$ it asserts the existence of a ring map $\rho_I : A \to \mathcal{O}_I$ lifting the structure map such that, writing `dom` for the set of $x \in$ [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186) whose $\overline{\mathbb{Q}}$-point `gpts x` factors through an $\mathcal{O}_I$-point of `D.toBase`, the following five clauses hold: $I$ fixes every element of `dom`; $\mathcal{O}_I$-points of `D.toBase` are determined by their associated $\overline{\mathbb{Q}}$-points; `dom` contains $0$ and is closed under differences; for every $n > 0$ prime to $p$, reduction to $\kappa$ is injective on the $n$-torsion of the group of $\mathcal{O}_I$-points and every $n$-torsion $\kappa$-point lifts to an $n$-torsion $\mathcal{O}_I$-point; and any Frobenius element at $p$ normalising $I$ preserves `dom`.
--
--   *The norm-free subgroup scheme.* $\mathcal{A}$ with $a : \mathcal{A} \to \operatorname{Spec} A$ and $\iota$ a morphism to `D.toBase` over $a$ satisfies the six clauses of `h𝒜`: $\iota$ is a closed immersion; $a$ is proper and smooth with connected geometric fibres; the image of $\mathcal{A}$ is stable under the identity, multiplication and inversion of the relative group law; the $\overline{\mathbb{Q}}$-points of $\mathcal{A}$ are exactly the points of the subgroup [`ModularCurve.normFreePartAt (M * p) p`](def/ModularCurve_X1PrimitiveSpecializationAtP.html#L29); and the image is stable under every $\varphi t$. The hypothesis `hF10` states that for every $\kappa$-algebra $T'$, any $T'$-point of `(D.baseChange κ).toBase` coming from $\mathcal{A}$ is annihilated by $\varphi$ of the sum over $b \in (\mathbb{Z}/p)^\times$ of the diamond generators attached to the Chinese-remainder lifts of $(b, 1)$ in $\mathbb{Z}/p \times \mathbb{Z}/M$, the result being the identity section.
--
--   *Igusa models, the Gauss reading and the nodes.* $w$ is an `IntegralWeightOneForm` over $\kappa$ of level $M$ (a weight-one form with integral $q$-expansion whose reduction is nonzero), and [`ModularCurve.igusaFunctionFieldX1C κ M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35) the associated Igusa function field. $Mdl_1$ and $Mdl_2$ are curve models of this field over $\kappa$ with isomorphisms $e_1 : Mdl_1.C \cong C_1$, $e_2 : Mdl_2.C \cong C_2$ over $\kappa$ (`he₁`, `he₂`), and `hne₁` provides a point of the relevant chart open on the first component. The hypothesis `hgauss₁` pins the first component as the component carrying $q$-expansions: for $a$ in the finite chart algebra and power series $x, y$ over $A$ with the reduction of $y$ nonzero and $a \cdot y = x$ as Laurent series over $L$, the germ of $a$ at the generic point of $C_1$, read in the Igusa function field, is the quotient of the reductions of $x$ and $y$. The hypothesis `hεgal` is the Galois equivariance of the cusp section $\varepsilon$ with respect to automorphisms of the two-chart model induced by coefficientwise Galois action. Further, `nodesIg` is a finite set of pairs of places of the Igusa function field, $\Psi$ an isomorphism of `G.J0s` with [`AlgebraicCurve.GluedPic0 κ (igusaFunctionFieldX1C κ M w) nodesIg`](def/AlgebraicCurve_GluedPic0.html#L201), and $\theta_1, \theta_2$ isomorphisms of `G.JI` and `G.JE` with `Pic0` of that field. The seven clauses of `hF4c` assert: a pair of places lies in `nodesIg` exactly when it comes from a $\kappa$-point of the intersection of $C_1$ and $C_2$; `nodesIg` has cardinality $n$; both projections are injective on `nodesIg`; $\Psi$ is compatible with `G.proj` through `GluedPic0.toPic0Pair` and $(\theta_1, \theta_2)$; the image of `G.torus` under $\Psi$ is the range of `GluedPic0.nodeUnit`; and $\theta_1$, $\theta_2$ compute classes as those of differences of the places of a point and of the respective cusp section. Finally `frobT` is a semilinear automorphism of the Igusa function field over $\kappa$ which raises every Laurent coefficient to the $p$-th power (`hfrobT`).
--
--   *The specialisation family.* For each quadruple $(I, hI, hI\mu, hIf)$ as in `hF3` there are given an additive subgroup `dom𝒟 I …` of [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186) and a homomorphism `sp𝒟 I …` from it to `GluedPic0 κ (igusaFunctionFieldX1C κ M w) nodesIg`. The two clauses of `hIFm` are the interface: $y$ lies in `dom𝒟 I …` exactly when `gpts y` factors through an $\mathcal{O}_I$-point of `D.toBase` (for the map chosen by `hF3`), and `sp𝒟 I … y` equals $\Psi$ applied to the element of `G.J0s` corresponding under `pts` to the reduction to $\kappa$ of that $\mathcal{O}_I$-point. The two clauses of `hlev` are the level compatibility: an $\mathcal{O}_I$-point extends to an $\mathcal{O}_J$-point for $J \le I$ with the same reduction to $\kappa$, and consequently membership in `dom𝒟 I …` implies membership in `dom𝒟 J …` with the same value of `sp𝒟`.
--
--   *Conclusion.* For all subgroups $I$ and $I'$ of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ contained in the inertia subgroup of $Pl$ over $\mathbb{Q}$, each acting trivially on the $p$-th roots of unity and of finite index in that inertia subgroup, and for every $y$ in [`ModularCurve.normFreePartAt (M * p) p`](def/ModularCurve_X1PrimitiveSpecializationAtP.html#L29) with $y \in$ `dom𝒟 I …` and [`ModularCurve.heckeOperatorOneBar (M * p) ⟨p, _⟩ y`](def/ModularCurve_X1HeckeModule.html#L36) $\in$ `dom𝒟 I' …`: if the second component of `GluedPic0.toPic0Pair` applied to `sp𝒟 I … y` vanishes, then the first component of `GluedPic0.toPic0Pair` applied to `sp𝒟 I' …` of [`ModularCurve.heckeOperatorOneBar (M * p) ⟨p, _⟩ y`](def/ModularCurve_X1HeckeModule.html#L36) equals $(p : \mathbb{Z})$ times the image under `frobT⁻¹` of the first component of `GluedPic0.toPic0Pair` applied to `sp𝒟 I … y`.
--
--   This is the Eichler–Shimura type congruence at $p$ in the form used for level lowering: on norm-free points of $J_1(Mp)$ whose specialisation lies on the component of the special fibre carrying the $q$-expansions (the Igusa component through the reduced cusp), the Hecke operator $U_p$ acts as $p$ times the inverse of the Frobenius semilinear automorphism of the Igusa curve. It is the $U_p$-clause in the assembly of the semistable specialisation package for $J_1(Mp)$ and is used by [`ModularCurve.exists_qExpSemistableSpecializationPinnedV3_family_normFreePart_and_diamond_of_dvd_of_not_sq_dvd_of_le_div`](thm.html#ModularCurve.exists_qExpSemistableSpecializationPinnedV3_family_normFreePart_and_diamond_of_dvd_of_not_sq_dvd_of_le_div).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_normFreePartFamily_toPic0Pair_sp_heckeOperatorOneBar_fst_eq_natCast_smul_frob_inv_smul_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.normFreePartFamily_toPic0Pair_sp_heckeOperatorOneBar_fst_eq_natCast_smul_frob_inv_smul_twoChartModel_x1_mul
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

      (∀ (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ)
          (hIμ : ∀ σ ∈ I, ∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ)
          (hIf : (I.subgroupOf (Pl.inertiaSubgroupIn ℚ)).FiniteIndex)
          (I' : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI' : I' ≤ Pl.inertiaSubgroupIn ℚ)
          (hI'μ : ∀ σ ∈ I', ∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ)
          (hI'f : (I'.subgroupOf (Pl.inertiaSubgroupIn ℚ)).FiniteIndex),
        ∀ y ∈ ModularCurve.normFreePartAt (M * p) p, ∀ (hy : y ∈ (dom𝒟 I hI hIμ hIf))
          (hUy : ModularCurve.heckeOperatorOneBar (M * p) ⟨p, Fact.out⟩ y ∈ (dom𝒟 I' hI' hI'μ hI'f)),
          (AlgebraicCurve.GluedPic0.toPic0Pair _ ((sp𝒟 I hI hIμ hIf) ⟨y, hy⟩)).2 = 0 →
          (AlgebraicCurve.GluedPic0.toPic0Pair _
              ((sp𝒟 I' hI' hI'μ hI'f) ⟨ModularCurve.heckeOperatorOneBar (M * p) ⟨p, Fact.out⟩ y, hUy⟩)).1 =
            (p : ℤ) • (frobT⁻¹ •
              (AlgebraicCurve.GluedPic0.toPic0Pair _ ((sp𝒟 I hI hIμ hIf) ⟨y, hy⟩)).1)) := by sorry
