-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_reduction_fst_valuationSubring_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_reduction_fst_valuationSubring_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/c7353691-0cd2-5896-84b2-31ede27264a8
-- title:
--   Pl-point of relative Pic⁰ representing 𝒪(ξ₁)⊗𝒪(ξ₂)⁻¹
-- statement:
--   Fix a prime $p$, an integer $M\ge 5$ with $p\nmid M$, a cyclotomic extension $L/\mathbb Q$ of conductor $p$ with primitive $p$-th root of unity $\zeta$, and let $K$ be the intermediate field of $L\subseteq\mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the image, under the coefficientwise map $\mathrm{coeffEmb}$, of the function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) of $X_1(Mp)$ over $\mathbb Q$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ lies in the image of $A$, with $K$ an $A$-algebra compatibly, and let $j\in K$ be the element whose Laurent expansion is the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), assumed non-zero; write $X=$ [`ModularCurve.TwoChartModel A K j`](def/ModularCurve_TwoChartModel.html#L229) with structure morphism $f=$ [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), assumed proper and flat, with smooth geometrically integral generic fibre of relative dimension $1$. Let $k$ be an algebraically closed $A$-algebra of characteristic $p$, and let $c_1:C_1\to\operatorname{Spec}k$, $c_2:C_2\to\operatorname{Spec}k$ be proper, smooth of relative dimension $1$ and geometrically integral, embedded by closed immersions $i_1,i_2$ into $X\times_A k$ over $k$, covering all points of $X\times_A k$ between them, with $C_1\times_{X\times_A k}C_2$ reduced of finite cardinality $n>0$. Let $\varepsilon$ be a section of $f$ over $\operatorname{Spec}A$, $\varepsilon_1,\varepsilon_2$ sections of $c_1,c_2$ with $\varepsilon_1$ followed by $i_1$ equal to the base change of $\varepsilon$ to $k$, and let $D$ be a relative $\mathrm{Pic}^0$ designation for $f$ (a scheme $P$ over $\operatorname{Spec}A$ with zero section) together with the datum $\mathrm{hrep}$ of a representation by $D$ of the subfunctor of $\varepsilon$-rigidified invertible modules on $X\times_A T$ which are fibrewise algebraically equivalent to zero. Let $U$ be an open subscheme of $X$, maximal among opens on which $f$ is smooth of relative dimension $1$. Let $\mathrm{Pl}$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit in it, $\rho:A\to\mathrm{Pl}$ a ring map inducing the structure map $A\to\overline{\mathbb Q}$, and $\pi_k:\mathrm{Pl}\to k$ a surjective ring map with $\pi_k\circ\rho$ the structure map $A\to k$. Then for all $\mathrm{Pl}$-points $\xi_1,\xi_2$ of $X$ over $\operatorname{Spec}\rho$ and all $k$-sections $d_1,d_2$ of $c_1$: if the set-theoretic images of $\xi_1$ and $\xi_2$ lie in $U$, and for $m=1,2$ the composite $d_m$, $i_m{=}i_1$, $\mathrm{pr}_1$ equals $\operatorname{Spec}\pi_k$ followed by $\xi_m$ while $(d_m$ followed by $i_1)$ sends the closed point of $\operatorname{Spec}k$ outside the image of $i_2$, then there is a $\mathrm{Pl}$-point $s$ of $P$ over $\operatorname{Spec}\rho$ such that the pullback along $s$ of the Poincaré bundle of $\mathrm{hrep}$ is isomorphic, as a module on $X\times_A\operatorname{Spec}\mathrm{Pl}$, to the tensor product of the dual of the ideal module of the relative effective Cartier divisor cut out by the graph of $\xi_1$ with the ideal module of the one cut out by the graph of $\xi_2$.
--
--   This identifies the class of $\mathcal O(\xi_1)\otimes\mathcal O(\xi_2)^{-1}$, for two $\mathrm{Pl}$-valued points of the two-chart stable model of $X_1(Mp)$ whose reductions lie on the component $C_1$ away from the crossings with $C_2$, as a $\mathrm{Pl}$-point of the scheme representing the fibrewise-algebraically-trivial rigidified Picard functor. It feeds the computation of the reduction map on degree-zero divisor classes for this model, being used in the results that express such a point's first component as a $\mathrm{Pic}^0$ class of a divisor supported on sections and its second component as zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_reduction_fst_valuationSubring_twoChartModel_x1_mul.lean

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
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_X1HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open AlgebraicGeometry.RelPicard

theorem ModularCurve.XOneP.exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_reduction_fst_valuationSubring_twoChartModel_x1_mul
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

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    [Flat (ModularCurve.TwoChart.modelTo A (↥K) j)]
    (hsmL : SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))
    (hgiL : GeometricallyIntegral (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))

    (U : (ModularCurve.TwoChartModel A (↥K) j).Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j))]
    (hUmax : ∀ W : (ModularCurve.TwoChartModel A (↥K) j).Opens, SmoothOfRelativeDimension 1 (W.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j)) → W ≤ U)

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hπk : Function.Surjective πk) :
    ∀ (ξ₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j)) (ξ₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j))
      (d₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (d₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      Set.range ξ₁.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) → Set.range ξ₂.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) →
      d₁.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ₁.1 →
      (d₁.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base →
      d₂.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ₂.1 →
      (d₂.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base →
      ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
        Nonempty ((hrep.some.poincare.pullbackAlong s).L ≅
          (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ξ₁.1 ξ₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ξ₂.1 ξ₂.2).idealModule) := by sorry
