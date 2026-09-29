-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_pts_reduction_and_exists_schemeHomOver_valuationSubring_of_pts_specialFibre_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_pts_reduction_and_exists_schemeHomOver_valuationSubring_of_pts_specialFibre_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/24583910-648f-5847-a3c6-5f521037da81
-- title:
--   Hensel lifting of k-points of D to Pl-points
-- statement:
--   The setting is the two-chart model of $X_1(Mp)$ over a discrete valuation ring and the scheme representing its relative $\mathrm{Pic}^0$, together with a full package of special-fibre, Galois, Hecke and Igusa data; the conclusion is a reduction statement for points with values in a valuation subring of $\overline{\mathbb Q}$.
--
--   **Arithmetic data.** A prime $p$ and a natural number $M$ with $5 \le M$ (`hM`) and $p \nmid M$ (`hpM`). A field $L$ of characteristic zero which is a cyclotomic extension of $\mathbb Q$ of type $\{p\}$, and an element $\zeta \in L$ which is a primitive $p$-th root of unity (`hζ`). An intermediate field $K$ of $L \subseteq \mathrm{LaurentSeries}\,L$ which by `hK` equals [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield generated over $L$ by the coefficientwise image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the function field of $X_1(Mp)$ over $\mathbb Q$ inside Laurent series over $\mathbb Q$. A discrete valuation ring $A$, a domain with $L$ as fraction field, such that $p$ lies in the maximal ideal of $A$ (`hAp`) and $\zeta$ lies in the image of $A \to L$ (`hζA`), with an $A$-algebra structure on $K$ compatible with $A \to L \to K$. An element $j \in K$, nonzero, whose image in $\mathrm{LaurentSeries}\,L$ is the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) (`hj`).
--
--   **The model.** The morphism [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252) from `TwoChartModel A ↥K j` to $\operatorname{Spec} A$, obtained from the structure maps of the two $A$-subalgebras `chartAlgFin` and `chartAlgInf` of $K$ glued over their common part; it is assumed proper.
--
--   **Special fibre and its two components.** An algebraically closed field $k$ of characteristic $p$ which is an $A$-algebra. Two schemes $C_1, C_2$ with morphisms $c_1, c_2$ to $\operatorname{Spec} k$ that are proper, smooth of relative dimension $1$ and geometrically integral, and closed immersions $i_1 : C_1 \to X_k$, $i_2 : C_2 \to X_k$ over $k$ into the special fibre $X_k = \mathrm{pullback}(\mathtt{modelTo}, \operatorname{Spec} k \to \operatorname{Spec} A)$ (so $i_\nu$ followed by the projection to $\operatorname{Spec} k$ is $c_\nu$). The hypothesis `hcover` states that every point of $X_k$ lies in the image of $i_1$ or of $i_2$; `hred` states that $\mathrm{pullback}\,i_1\,i_2$ is reduced, and `hn`, `hn0` give its cardinality as a number $n > 0$.
--
--   **Sections.** A section $\varepsilon$ of `modelTo` over $\operatorname{Spec} A$, sections $\varepsilon_1, \varepsilon_2$ of $c_1, c_2$, and `hε₁`: $\varepsilon_1$ followed by $i_1$ equals the base-changed section `sectionBaseChange k ε`.
--
--   **Representability of relative $\mathrm{Pic}^0$.** A datum $D$ consisting of a scheme $D.P$, a morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} A$ and a zero section. The hypothesis `hrep` asserts that $D$ represents, with respect to $\varepsilon$, the subfunctor of rigidified line bundles cut out by `algEquivZeroCut` (fibrewise algebraic equivalence to zero): it provides a Poincaré bundle on $D.\mathrm{toBase}$ satisfying the condition, the universal property that every such rigidified bundle on a test base is induced by a unique point of $D.\mathrm{toBase}$, and triviality along the zero section. Further, `hsm` and `hsep`: $D.\mathrm{toBase}$ is smooth and separated. The hypothesis `hreps` is the corresponding representability statement for the base change of the model and of $D$ to $k$, and `hPk` an isomorphism between its Poincaré bundle and the one obtained from `hrep` by base change to $k$. Data $D_1, D_2$ with `hrep₁`, `hrep₂` represent relative $\mathrm{Pic}^0$ of $c_1$, $c_2$ with respect to $\varepsilon_1$, $\varepsilon_2$.
--
--   **The map to the $C_2$-Jacobian.** A morphism $\nu_2$ from $(D.\mathrm{baseChange}\,k).\mathrm{toBase}$ to $D_2.\mathrm{toBase}$ over $\operatorname{Spec} k$, with `hν₂`: for every $k$-scheme $t$ and every point $a$ of $(D.\mathrm{baseChange}\,k).\mathrm{toBase}$ over $t$, the pullback of the Poincaré bundle of $D_2$ along $a$ followed by $\nu_2$ is isomorphic to the rigidification, along `rigSection c₂ t ε₂` relative to the projection $\mathrm{pullback}\,c_2\,t \to T$, of the pullback along `curveChange i₂` of the bundle obtained from `hreps` at $a$.
--
--   **Geometric generic fibre, $q$-expansions and Galois action.** Compatible algebra structures of $A$ and $L$ in $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`. A curve model $M_\eta$ over $\overline{\mathbb Q}$ of the function field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) (a proper, smooth of relative dimension $1$, integral scheme with an identification of its function field, a bijection between its closed points and the places, and the attendant stalk and affineness clauses), an isomorphism $e_\eta$ from $M_\eta.C$ to the base change of the model to $\overline{\mathbb Q}$ with `heη` saying that $e_\eta$ followed by the projection to $\operatorname{Spec}\overline{\mathbb Q}$ is $M_\eta.\mathrm{toBase}$, a nonemptiness instance for the preimage of the finite chart, and `hMηpin`: for every element $a$ of `chartAlgFin`, the element of the function field obtained from $a$ by taking its germ at the generic point along $e_\eta$ followed by the finite-chart projection has, as a Laurent series over $\overline{\mathbb Q}$, the coefficientwise image of the Laurent series of $a$ over $L$. The hypothesis `hgal` states that for every $g \in \mathrm{Aut}(\overline{\mathbb Q}/\mathbb Q)$ fixing $L$ pointwise and all $\overline{\mathbb Q}$-points $x, x'$ of $M_\eta.C$, if $x'$ followed by the chart projection equals $\operatorname{Spec} g$ followed by $x$ followed by the chart projection, then the place attached to $x'$ is the image of the place attached to $x$ under the action of $g$ through [`ModularCurve.arithmeticGalois`](def/ModularCurve_ArithmeticGalois.html#L54).
--
--   **Special-fibre group combinatorics.** A datum $G$ of type [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9): abelian groups $J_{0s}$, $J_I$, $J_E$, a subgroup `torus` of $J_{0s}$, and a surjective homomorphism $\mathrm{proj} : J_{0s} \to J_I \times J_E$ with kernel `torus`. Bijections `pts`, `ptsI`, `ptsE` of $J_{0s}$, $J_I$, $J_E$ with the $k$-points of $(D.\mathrm{baseChange}\,k).\mathrm{toBase}$, $D_1.\mathrm{toBase}$, $D_2.\mathrm{toBase}$ respectively (sections over the identity of $\operatorname{Spec} k$). The hypotheses `hadd`, `haddI`, `haddE` say that each of these bijections is additive in the sense that the Poincaré bundle pulled back at a sum of points is isomorphic to the tensor product of its pullbacks at the two points. The hypothesis `hproj` says that for every $x \in J_{0s}$ the first component of $\mathrm{proj}\,x$ corresponds under `ptsI` to `pts x` followed by the morphism `RepresentsRelSubPic.pullbackHom` attached to $i_1$ and `hε₁`, and the second component corresponds under `ptsE` to `pts x` followed by $\nu_2$.
--
--   **Generic points, group law and Hecke operators.** A bijection `gpts` from [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186), the degree-zero divisor class group of `x1FunctionFieldBar (M * p)`, to the $\overline{\mathbb Q}$-points of $D.\mathrm{toBase}$ over $\operatorname{Spec} A$, with `hgadd` saying that it is additive for the relative group law supplied by `hrep`. A map $\varphi$ from [`ModularCurve.HeckeAlgOne`](def/ModularCurve_X1HeckeModule.html#L16) to endomorphisms of $D.\mathrm{toBase}$ over $\operatorname{Spec} A$, with `hφmul`: each $\varphi(t)$ is a homomorphism for the relative group law on all test bases; and `hφpts`: for the Hecke module structure `heckeModuleOneBar (M * p)`, $\mathrm{gpts}(t \cdot x)$ is $\mathrm{gpts}(x)$ followed by $\varphi(t)$.
--
--   **Abel–Jacobi data over $L$ and over $\overline{\mathbb Q}$.** The representability statement `hDL` for the base change to $L$ with the section `sectionBaseChange L ε`; a morphism $\mathrm{ajL}$ from the base-changed curve over $L$ to $(D.\mathrm{baseChange}\,L).\mathrm{toBase}$ over $L$; a comparison morphism $k_L$ from the $\overline{\mathbb Q}$-fibre to the $L$-fibre of the model; a morphism $\overline{\mathrm{aj}}$ from $M_\eta.C$ to $D.P$; a $\overline{\mathbb Q}$-point $\overline\varepsilon$ of $M_\eta.C$. The accompanying hypotheses are: `hPL`, comparison of the Poincaré bundle of `hDL` with the base change to $L$ of the one from `hrep`; `hajLε`, the base-changed section followed by $\mathrm{ajL}$ is the zero section; `hajL`, for every field $K'$, every morphism $t$ from $\operatorname{Spec} K'$ to $\operatorname{Spec} L$ and every point $x$ of the curve over $t$, the Poincaré bundle pulled back along $x$ followed by $\mathrm{ajL}$ is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor of the base point, i.e. $\mathrm{ajL}$ realises $x \mapsto [x]-[\varepsilon]$; `hkL₁`, `hkL₂`, compatibility of $k_L$ with both projections; `hajbar`, $\overline{\mathrm{aj}} = e_\eta$ followed by $k_L$, $\mathrm{ajL}$ and the first projection; `hajbar_over`, $\overline{\mathrm{aj}}$ lies over $M_\eta.\mathrm{toBase}$; `hεbar`, $\overline\varepsilon$ followed by $e_\eta$ and the chart projection is $\varepsilon$ base changed; `hεbar_aj`, $\overline\varepsilon$ followed by $\overline{\mathrm{aj}}$ is the zero section; and `hpts_aj`, for all $\overline{\mathbb Q}$-points $x, s$ of $M_\eta.C$ with $s$ the base point, there is a degree-zero divisor equal to $[\,\text{place of }x\,] - [\,\text{place of }s\,]$ whose class maps under `gpts` to $x$ followed by $\overline{\mathrm{aj}}$.
--
--   **Igusa curve identification of the first component.** An integral weight-one form $w$ for $\Gamma_1(M)$ over $k$ (a modular form together with an integral $q$-expansion whose reduction in $k$ is nonzero); a curve model $\mathrm{Mdl}_1$ over $k$ of the Igusa function field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), an isomorphism $e_1$ from $\mathrm{Mdl}_1.C$ to $C_1$ with `he₁`: $e_1$ followed by $c_1$ is $\mathrm{Mdl}_1.\mathrm{toBase}$; a nonemptiness instance `hne₁` for the relevant chart preimage; and `hgauss₁`, a Gauss-type reading of the chart coordinates: for every $a$ in `chartAlgFin` and all power series $x, y$ over $A$ with $y$ having nonzero reduction, if $a \cdot y = x$ as Laurent series over $L$, then the element of the Igusa function field obtained from $a$ along $e_1$, $i_1$ and the finite-chart projection equals the quotient of the reductions of $x$ and $y$ as Laurent series over $k$.
--
--   **Divisor-class and Frobenius data on the Igusa side.** An additive isomorphism $\theta_1$ from $J_I$ to the degree-zero class group $\mathrm{Pic}^0$ of the Igusa function field, with `hθpin₁`: if for some $k$-point $x$ of $c_1$ the Poincaré pullback at $\mathrm{ptsI}\,g$ is isomorphic to the line bundle of $x$ tensored with the ideal module of $\varepsilon_1$, then there is a degree-zero divisor equal to $[\,\text{place of }x\,]-[\,\text{place of }\varepsilon_1\,]$ whose class is $\theta_1 g$. A semilinear automorphism $\mathrm{frobIg}$ of the Igusa function field over $k$ acting on Laurent coefficients by $p$-th powers (`hfrobIg`).
--
--   **The identity-component subgroup scheme.** A scheme $\mathcal A$ with a morphism $a$ to $\operatorname{Spec} A$ and a closed immersion $\iota$ from $\mathcal A$ to $D.P$ over $a$ (`h𝒜cl`), with $a$ proper (`h𝒜pr`) and smooth (`h𝒜sm`), all geometric fibres connected (`h𝒜conn`), and `h𝒜grp`: on every test base the image of $\iota$ contains the unit and is closed under the product and inverse of the relative group law attached to `hrep`. The hypothesis `h𝒜gen` states that a class $x$ in [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186) lies in [`ModularCurve.normFreePartAt (M * p) p`](def/ModularCurve_X1PrimitiveSpecializationAtP.html#L29) if and only if $\mathrm{gpts}\,x$ factors through $\iota$, and `h𝒜hecke` that the image of $\iota$ is stable under each $\varphi(t)$.
--
--   **Valuation-theoretic data.** A valuation subring $\mathrm{Pl}$ of $\overline{\mathbb Q}$ with $p$ a nonunit of $\mathrm{Pl}$ (`hPl`, the predicate `LiesOverPrime p`); a ring homomorphism $\rho : A \to \mathrm{Pl}$ lifting $A \to \overline{\mathbb Q}$ (`hρ`); a subring $O$ of $\overline{\mathbb Q}$ contained in $\mathrm{Pl}$ (`hO`) together with $\rho_O : A \to O$ lifting $A \to \overline{\mathbb Q}$ (`hρO`); and a ring homomorphism $\pi_k : \mathrm{Pl} \to k$ with $A \to k$ equal to $\pi_k \circ \rho$ (`hAlgk`) and $\pi_k$ surjective (`hπk`).
--
--   **Conclusion.** The conjunction of two assertions about the reduction of points with values in $\mathrm{Pl}$.
--
--   First, for every morphism $zz$ from $\operatorname{Spec}\mathrm{Pl}$ to $D.P$ lying over $\operatorname{Spec}\rho : \operatorname{Spec}\mathrm{Pl} \to \operatorname{Spec} A$, there exists $t \in J_{0s}$ such that the $k$-point $\mathrm{pts}\,t$ of the special fibre, composed with the projection $\mathrm{pullback}(D.\mathrm{toBase}, \operatorname{Spec} k \to \operatorname{Spec} A) \to D.P$, equals $\operatorname{Spec}\pi_k$ followed by $zz$.
--
--   Second, for every $t \in J_{0s}$ there exists such a morphism $zz$ from $\operatorname{Spec}\mathrm{Pl}$ to $D.P$ over $\operatorname{Spec}\rho$ satisfying the same equality: $\mathrm{pts}\,t$ followed by the projection to $D.P$ equals $\operatorname{Spec}\pi_k$ followed by $zz$.
--
--   This is the Hensel lifting step in the Raynaud-style analysis of the Néron/$\mathrm{Pic}^0$ model of $J_1(Mp)$ over a discrete valuation ring: the $k$-points of the special fibre of $D$, as parametrised by the special-fibre datum $G$, are exactly the reductions of the $\mathrm{Pl}$-valued points of $D$, the valuation ring $\mathrm{Pl}$ of $\overline{\mathbb Q}$ being Henselian with residue map $\pi_k$ onto $k$ and $D \to \operatorname{Spec} A$ smooth. It feeds the identification of the Hecke and Frobenius action on the special fibre used in the level-lowering arguments at $p$, and is cited by the statements comparing $\mathrm{proj}$-components of reductions of norm-free classes with the Igusa-curve Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_pts_reduction_and_exists_schemeHomOver_valuationSubring_of_pts_specialFibre_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
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
import Definitions.Def_ModularCurve_JOnePOpsV2
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
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_X1HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_pts_reduction_and_exists_schemeHomOver_valuationSubring_of_pts_specialFibre_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε k
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩)).L))
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation k c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange k).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t (D.baseChange k).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

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

    (G : ModularCurve.JOneP.NeronSpecialFibreGeom p)
    (pts : G.J0s ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (ptsI : G.JI ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₁.toBase)
    (ptsE : G.JE ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase)
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
    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))
    (φ : ModularCurve.HeckeAlgOne → SchemeHomOver D.toBase D.toBase)
    (hφmul : ∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s x y) (φ t) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
          (NeronModelInfra.schemeHomOverComp x (φ t)) (NeronModelInfra.schemeHomOverComp y (φ t)))
    (hφpts : letI := ModularCurve.heckeModuleOneBar (M * p)
      ∀ (t : ModularCurve.HeckeAlgOne) (x : ModularCurve.JOne (M * p)), (gpts (t • x)).1 = (gpts x).1 ≫ (φ t).1)

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

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)

    [hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hgauss₁ : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A k) ≠ 0 →
      ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      ((Mdl₁.ffEquiv.symm
          (Mdl₁.C.germToFunctionField ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) =
        HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) / HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k)))

    (θ₁ : G.JI ≃+ AlgebraicCurve.Pic0 k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hθpin₁ : ∀ (g : G.JI) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      Nonempty ((hrep₁.some.poincare.pullbackAlong (ptsI g)).L ≅
        (RelEffCartierDiv.ofPoint c₁ x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₁ ε₁.1 ε₁.2).idealModule) →
      ∃ Dv : Divisor.degZero (K := k) (F := ↥(ModularCurve.igusaFunctionFieldX1C k M w)),
        (Dv : Divisor k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) =
          Finsupp.single (Mdl₁.pointEquivPlace ⟨x.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact x.2⟩) 1 -
            Finsupp.single (Mdl₁.pointEquivPlace ⟨ε₁.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact ε₁.2⟩) 1 ∧
        θ₁ g = Pic0.mk Dv)

    (frobIg : SemilinearAut k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hfrobIg : ∀ (x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (n : ℤ),
      ((frobIg • x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k).coeff n = ((x : LaurentSeries k).coeff n) ^ p)

    (𝒜 : Scheme.{0}) (a : 𝒜 ⟶ Spec (CommRingCat.of A)) (ι : SchemeHomOver a D.toBase)

    (h𝒜cl : IsClosedImmersion ι.1)

    (h𝒜pr : IsProper a) (h𝒜sm : Smooth a)
    (h𝒜conn : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
        ConnectedSpace ↥(pullback a s))

    (h𝒜grp : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)),
        (∃ o : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp o ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).one s) ∧
        (∀ x y : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
            (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι)) ∧
        (∀ x : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).inv s
            (NeronModelInfra.schemeHomOverComp x ι)))

    (h𝒜gen : ∀ x : ModularCurve.JOne (M * p),
        x ∈ ModularCurve.normFreePartAt (M * p) p ↔
          ∃ y : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) a, y.1 ≫ ι.1 = (gpts x).1)

    (h𝒜hecke : ∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x : SchemeHomOver s a),
        ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x ι) (φ t))

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ)) (hO : O ≤ Pl.toSubring)
    (ρO : A →+* ↥O) (hρO : O.subtype.comp ρO = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hπk : Function.Surjective ⇑πk) :
    (∀ zz : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
      ∃ t : G.J0s, (pts t).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ zz.1) ∧
    ∀ t : G.J0s,
      ∃ zz : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase, (pts t).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ zz.1 := by sorry
