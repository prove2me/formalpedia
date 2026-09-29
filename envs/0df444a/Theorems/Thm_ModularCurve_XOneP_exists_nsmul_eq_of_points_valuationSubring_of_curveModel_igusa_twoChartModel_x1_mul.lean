-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_nsmul_eq_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_nsmul_eq_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/64ca3298-3998-595a-8510-1c99ec6f9e8f
-- title:
--   Prime-to-p divisibility of finite torsion classes in J₁(Mp)
-- statement:
--   **Arithmetic data.** Fix a prime $p$ and a positive integer $M$ with $5 \le M$ and $p \nmid M$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K$ be an intermediate field of the Laurent series field $\mathrm{LaurentSeries}\,L$ over $L$, assumed (hypothesis `hK`) to be [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield generated over $L$ by the coefficientwise image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the function field of $X_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with an $L$-algebra structure making $L$ its fraction field, such that $p$ lies in the maximal ideal of $A$ (`hAp`) and $\zeta$ lies in the image of $A$ (`hζA`), with $K$ an $A$-algebra compatibly with $L$. Let $j$ be a nonzero element of $K$ whose image in $\mathrm{LaurentSeries}\,L$ is the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular $j$-invariant (`hj`). Write $X =$ [`ModularCurve.TwoChart.modelTo A (↥K) j`](def/ModularCurve_TwoChartModel.html#L252) for the associated two-chart model over $\operatorname{Spec} A$, glued from the spectra of the two chart algebras `chartAlgFin` and `chartAlgInf`, and assumed proper.
--
--   **Data over the residue field.** Let $k$ be an algebraically closed field of characteristic $p$ and an $A$-algebra, and write $X_k$ for the base change `baseChange A X k`, the second projection of $X \times_{\operatorname{Spec} A} \operatorname{Spec} k$. Let $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $i_1, i_2$ be morphisms over $\operatorname{Spec} k$ from $C_1$, $C_2$ to $X_k$ which are closed immersions. The hypothesis `hcover` states that every point of the scheme $X \times_{\operatorname{Spec} A} \operatorname{Spec} k$ lies in the image of $i_1$ or of $i_2$; `hred` states that the fibre product of $i_1$ and $i_2$ is reduced; and `hn`, `hn0` state that the number of its points equals $n$, with $n > 0$. Let $\varepsilon$ be a section of $X$ over $\operatorname{Spec} A$, and $\varepsilon_1, \varepsilon_2$ sections of $c_1, c_2$, with `hε₁` asserting that $\varepsilon_1$ followed by $i_1$ is the base-changed section `sectionBaseChange k ε`.
--
--   **Relative Picard data.** Let $D$ be a `RelativePic0Designation` for $X$, that is, a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} A$ and a zero section. The hypothesis `hrep` provides a `RepresentsRelSubPic` datum for $X$, $\varepsilon$ and the cut `algEquivZeroCut` (whose condition on a rigidified line bundle is `FibrewiseAlgEquivZero`): $D.\mathrm{toBase}$ carries a Poincaré rigidified line bundle satisfying that condition, every such bundle over a base $T$ is the pullback of the Poincaré bundle along a unique $T$-point of $D.\mathrm{toBase}$, and the pullback along the zero section is trivial. Further, $D.\mathrm{toBase}$ is smooth (`hsm`) and separated (`hsep`). The hypothesis `hreps` is the analogous representability datum for $X_k$, `sectionBaseChange k ε` and `D.baseChange k`, and `hPk` asserts that its Poincaré bundle is isomorphic to the base change `BaseChange.ofR` of the pullback of the Poincaré bundle of `hrep.some` along the first projection of `D.baseChange k`. Likewise $D_1$, $D_2$ are designations for $c_1$, $c_2$ with representability data `hrep₁`, `hrep₂`. Finally $\nu_2$ is a morphism over $\operatorname{Spec} k$ from $(D.\mathrm{baseChange}\,k).\mathrm{toBase}$ to $D_2.\mathrm{toBase}$ such that (`hν₂`) for every $k$-scheme $T$ and every $T$-point $a$ of $(D.\mathrm{baseChange}\,k).\mathrm{toBase}$, the pullback of the Poincaré bundle of `hrep₂.some` along $a$ followed by $\nu_2$ is isomorphic to the `Scheme.Modules.rigidify` of the pullback along `curveChange i₂.1 i₂.2 t` of the pullback of the Poincaré bundle of `hreps` along $a$, the rigidification being taken along `rigSection c₂ t ε₂` and the projection `pullback.snd c₂ t`; thus $\nu_2$ realises restriction of line bundles along $i_2$.
--
--   **The geometric generic fibre.** With $\overline{\mathbb{Q}}$ an $A$-algebra and an $L$-algebra compatibly, let $M_\eta$ be a `CurveModel` over $\overline{\mathbb{Q}}$ of the field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182): an integral proper scheme, smooth of relative dimension $1$ over $\operatorname{Spec} \overline{\mathbb{Q}}$, with a ring isomorphism of that field onto its function field over the base, a bijection between its closed points and the places of the field, the stalk-range condition identifying stalks with valuation subrings, and the property that every finite set of points lies in an affine open. Let $e_\eta : M_\eta.C \to X \times_{\operatorname{Spec} A} \operatorname{Spec}\overline{\mathbb{Q}}$ be an isomorphism compatible with the structure morphisms (`heη`). The instance `Mη_chart_nonempty` asserts that the open subscheme of $M_\eta.C$ obtained by pulling back, along $e_\eta$ followed by the first projection, the open image of the finite chart [`ModularCurve.TwoChart.ιFin A (↥K) j`](def/ModularCurve_TwoChartModel.html#L231) is nonempty. The hypothesis `hMηpin` asserts that for every element $a$ of the finite chart algebra [`ModularCurve.TwoChart.chartAlgFin A (↥K) j`](def/ModularCurve_TwoChartModel.html#L135), the element of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) corresponding under $M_\eta.\mathrm{ffEquiv}^{-1}$ to the germ of $a$ at the generic point of that open has Laurent expansion equal to the image under [`ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ))`](def/ModularCurve_LaurentCoeff.html#L16) of the expansion of $a$ in $\mathrm{LaurentSeries}\,L$. The hypothesis `hgal` asserts Galois equivariance: for every $\mathbb{Q}$-algebra automorphism $g$ of $\overline{\mathbb{Q}}$ fixing the image of $L$ pointwise, and all $\overline{\mathbb{Q}}$-points $x, x'$ of $M_\eta.C$ over its structure morphism, if $x'$ followed by $e_\eta$ and the first projection equals $\operatorname{Spec}(g)$ followed by $x$ and the same composite, then $M_\eta.\mathrm{pointEquivPlace}\,x'$ is the image of $M_\eta.\mathrm{pointEquivPlace}\,x$ under the action of [`ModularCurve.arithmeticGalois (ModularCurve.x1FunctionField (M * p)) g`](def/ModularCurve_ArithmeticGalois.html#L54).
--
--   **Group structure on the special fibre.** Let $G$ be a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9): abelian groups $G.J_{0s}$, $G.J_I$, $G.J_E$, a subgroup $G.\mathrm{torus}$ of $G.J_{0s}$, and a surjective homomorphism $G.\mathrm{proj} : G.J_{0s} \to G.J_I \times G.J_E$ with kernel $G.\mathrm{torus}$. Bijections `pts`, `ptsI`, `ptsE` identify these three groups with the sets of $k$-points of $(D.\mathrm{baseChange}\,k).\mathrm{toBase}$, $D_1.\mathrm{toBase}$, $D_2.\mathrm{toBase}$ respectively; the hypotheses `hadd`, `haddI`, `haddE` state that each bijection carries sums to points whose Poincaré pullbacks are isomorphic to the tensor product of the Poincaré pullbacks at the summands; and `hproj` states that for every $x$ in $G.J_{0s}$, `ptsI` of the first component of $G.\mathrm{proj}\,x$ is `pts x` followed by the classifying morphism `RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some`, and `ptsE` of the second component is `pts x` followed by $\nu_2$.
--
--   **Igusa identification of the components.** Let $w$ be a [`ModularCurve.IntegralWeightOneForm k M`](def/ModularCurve_IgusaFunctionFieldX1.html#L16), that is, a weight-one modular form on $\Gamma_1(M)$ together with an integral power series which is its $q$-expansion and whose reduction to $k$ has nonvanishing relevant coefficient, and let $\mathrm{Mdl}_1$, $\mathrm{Mdl}_2$ be curve models over $k$ of the Igusa function field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), with isomorphisms $e_1 : \mathrm{Mdl}_1.C \cong C_1$ and $e_2 : \mathrm{Mdl}_2.C \cong C_2$ compatible with the structure morphisms (`he₁`, `he₂`).
--
--   **Parametrisation of $J_1(Mp)$ by points of $D$.** Let `gpts` be a bijection from [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186), the group $\mathrm{Pic}^0$ of degree-zero divisor classes of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) over $\overline{\mathbb{Q}}$, onto the set of $\overline{\mathbb{Q}}$-points of $D.\mathrm{toBase}$ over `specMap A (AlgebraicClosure ℚ)`, additive for the relative group law `RepresentsRelSubPic.relativeGroupLaw` attached to `hrep.some` and the cut `algEquivZeroGroupCut` (`hgadd`). The remaining data realise this bijection through an Abel–Jacobi morphism: a representability datum `hDL` for the base change of $X$ to $L$, a morphism $\mathrm{ajL}$ over the base from that base change to $(D.\mathrm{baseChange}\,L).\mathrm{toBase}$, a morphism $k_L$ from $X \times_{\operatorname{Spec} A}\operatorname{Spec}\overline{\mathbb{Q}}$ to $X \times_{\operatorname{Spec} A}\operatorname{Spec} L$, a morphism $\overline{\mathrm{aj}} : M_\eta.C \to D.P$ and a $\overline{\mathbb{Q}}$-point $\overline{\varepsilon}$ of $M_\eta.C$, subject to: `hPL`, the base-change compatibility of Poincaré bundles over $L$ analogous to `hPk`; `hajLε`, that the base-changed section composed with $\mathrm{ajL}$ is the zero section of `D.baseChange L`; `hajL`, that for every field $K'$, every morphism $t : \operatorname{Spec} K' \to \operatorname{Spec} L$ and every $K'$-point $x$ of the base change of $X$ to $L$, the pullback of the Poincaré bundle of `hDL` along $x$ followed by $\mathrm{ajL}$ is isomorphic to the line bundle (the inverse ideal module) of `RelEffCartierDiv.ofPoint` at $x$ tensored with the ideal module of `RelEffCartierDiv.ofPoint` at the base point $t$ followed by the base-changed section, so that $\mathrm{ajL}$ classifies $(x) - (\varepsilon)$; `hkL₁` and `hkL₂`, that $k_L$ is compatible with the first projections and carries the second projection to the second projection followed by `specMap L (AlgebraicClosure ℚ)`; `hajbar`, that $\overline{\mathrm{aj}}$ is $e_\eta$ followed by $k_L$, $\mathrm{ajL}$ and the first projection of `D.baseChange L`; `hajbar_over`, that $\overline{\mathrm{aj}}$ followed by $D.\mathrm{toBase}$ is $M_\eta.\mathrm{toBase}$ followed by `specMap A (AlgebraicClosure ℚ)`; `hεbar` and `hεbar_aj`, that $\overline{\varepsilon}$ followed by $e_\eta$ and the first projection is `specMap A (AlgebraicClosure ℚ)` followed by $\varepsilon$, and that $\overline{\varepsilon}$ followed by $\overline{\mathrm{aj}}$ is `specMap A (AlgebraicClosure ℚ)` followed by the zero section of $D$; and `hpts_aj`, that for all $\overline{\mathbb{Q}}$-points $x, s$ of $M_\eta.C$ with $s$ the base point in the sense of `hεbar`, there is a degree-zero divisor $D_v$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) equal to the place of $x$ minus the place of $s$, each with multiplicity one, whose class satisfies $\mathrm{gpts}([D_v]) = x$ followed by $\overline{\mathrm{aj}}$.
--
--   **The place above $p$.** Let $\mathrm{Pl}$ be a valuation subring of $\overline{\mathbb{Q}}$ with `LiesOverPrime p`, that is, $p$ is a nonunit of $\mathrm{Pl}$; let $\rho : A \to \mathrm{Pl}$ be a ring homomorphism whose composite with the inclusion $\mathrm{Pl} \hookrightarrow \overline{\mathbb{Q}}$ is the structure map $A \to \overline{\mathbb{Q}}$, and $\pi_k : \mathrm{Pl} \to k$ a surjective ring homomorphism with $\pi_k \circ \rho$ the structure map $A \to k$.
--
--   **Conclusion.** Let $m, d$ be positive integers with $p \nmid md$. Then for every $y$ in [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186) with $m \cdot y = 0$, and every $\mathrm{Pl}$-point $z$ of $D.\mathrm{toBase}$ over $\operatorname{Spec}(\rho)$ such that the $\overline{\mathbb{Q}}$-point $\mathrm{gpts}\,y$ is $\operatorname{Spec}$ of the inclusion $\mathrm{Pl} \hookrightarrow \overline{\mathbb{Q}}$ followed by $z$, there exist an element $y'$ of [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186) and a $\mathrm{Pl}$-point $z'$ of $D.\mathrm{toBase}$ over $\operatorname{Spec}(\rho)$ such that $(m d) \cdot y' = 0$, the $\overline{\mathbb{Q}}$-point $\mathrm{gpts}\,y'$ is $\operatorname{Spec}$ of the inclusion $\mathrm{Pl} \hookrightarrow \overline{\mathbb{Q}}$ followed by $z'$, and $d \cdot y' = y$.
--
--   This is the divisibility step for the finite part of $J_1(Mp)$ at a place above $p$: classes whose $\overline{\mathbb{Q}}$-point on the relative $\mathrm{Pic}^0$ of the two-chart model extends to a point over the valuation ring $\mathrm{Pl}$ form a subgroup in which torsion is divisible by integers prime to $p$, the special fibre being an extension involving the Jacobians of the two Igusa curves and a torus. It feeds the computation of the Weil pairing between the toric and the finite parts in [`ModularCurve.XOneP.weilDatum_pairing_eq_one_of_proj_eq_zero_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.weilDatum_pairing_eq_one_of_proj_eq_zero_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul), the orthogonality input to level lowering at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_nsmul_eq_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul.lean

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
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_nsmul_eq_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul
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

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    (Mdl₂ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₂ : Mdl₂.C ≅ C₂)
    (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))

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

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : Function.Surjective πk)
    (m d : ℕ) (hm0 : 0 < m) (hd0 : 0 < d) (hpmd : ¬ p ∣ m * d) :
    ∀ (y : ModularCurve.JOne (M * p)), m • y = 0 →
      ∀ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase), (gpts y).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1 →
        ∃ (y' : ModularCurve.JOne (M * p)) (z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase),
          (m * d) • y' = 0 ∧ (gpts y').1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z'.1 ∧ d • y' = y := by sorry
