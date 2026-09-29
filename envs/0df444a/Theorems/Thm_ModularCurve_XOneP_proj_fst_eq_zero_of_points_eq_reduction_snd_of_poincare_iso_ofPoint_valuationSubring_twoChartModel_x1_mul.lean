-- Prove2me | Theorems.Thm_ModularCurve_XOneP_proj_fst_eq_zero_of_points_eq_reduction_snd_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.proj_fst_eq_zero_of_points_eq_reduction_snd_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/9b8c3c9f-6ca1-59bb-9400-7803ac5ccb9e
-- title:
--   Vanishing J_I-coordinate when both reductions avoid C₁
-- statement:
--   Fix a prime $p$ and $M\ge 5$ with $p\nmid M$; let $L$ be a field of characteristic zero that is a $\{p\}$-cyclotomic extension of $\mathbb Q$, $\zeta\in L$ a primitive $p$-th root of unity, and $K$ the intermediate field of $L((t))$ over $L$ obtained as $L$-adjunction of the coefficientwise image of the function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) of $X_1(Mp)$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A$, with $K$ an $A$-algebra compatibly, and let $j\in K$ be a nonzero element whose Laurent expansion is the image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157); write $X=$ [`ModularCurve.TwoChartModel A K j`](def/ModularCurve_TwoChartModel.html#L229) with its structure morphism $\pi=$ [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), assumed proper. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$, and $c_1:C_1\to\operatorname{Spec} k$, $c_2:C_2\to\operatorname{Spec} k$ proper, smooth of relative dimension $1$, geometrically integral, together with closed immersions $i_1,i_2$ of $C_1,C_2$ into the base change $X\times_A k$ whose images cover that base change, with reduced intersection $C_1\times_{X_k}C_2$ of finite cardinality $n>0$. Sections $\varepsilon$ of $\pi$ and $\varepsilon_1,\varepsilon_2$ of $c_1,c_2$ are given with $\varepsilon_1$ followed by $i_1$ equal to the base change of $\varepsilon$. Further data: a designation $D$ (a scheme over $\operatorname{Spec} A$ with a zero section) representing, via some `RepresentsRelSubPic`, the subfunctor of rigidified line bundles on $X$ that are fibrewise algebraically equivalent to zero, with $D\to\operatorname{Spec} A$ smooth and separated; a representability datum `hreps` for the corresponding functor after base change to $k$, with its Poincaré bundle identified with the base change of the Poincaré bundle of $D$; designations $D_1,D_2$ with representability data for $c_1,c_2$; a morphism $\nu_2$ over $k$ from $D\times_A k$ to $D_2$ whose pull-backs of the Poincaré bundle of $D_2$ agree with the rigidified restriction along $i_2$ of the Poincaré bundle of `hreps`; algebra structures of $A$ and $L$ in $\overline{\mathbb Q}$; a datum $G$ consisting of abelian groups $J^0_s$, $J_I$, $J_E$, a subgroup $\mathrm{torus}\le J^0_s$ and a surjection $\mathrm{proj}:J^0_s\to J_I\times J_E$ with kernel $\mathrm{torus}$; bijections $\mathrm{pts},\mathrm{pts}_I,\mathrm{pts}_E$ from $J^0_s,J_I,J_E$ to the $k$-points of $D\times_A k$, $D_1$, $D_2$ that are additive for the Poincaré pull-backs up to isomorphism and compatible with $\mathrm{proj}$ through the restriction morphism along $i_1$ and through $\nu_2$; the largest open $U\subseteq X$ smooth of relative dimension $1$ over $\operatorname{Spec} A$; and a valuation subring $Pl$ of $\overline{\mathbb Q}$ with $p$ a nonunit, a ring map $\rho:A\to Pl$ inducing the structure map to $\overline{\mathbb Q}$, and a surjection $\pi_k:Pl\to k$ with $\pi_k\circ\rho$ the structure map $A\to k$. The conclusion asserts: for all $Pl$-points $\xi_1,\xi_2$ of $X$ over $\operatorname{Spec}\rho$ whose set-theoretic images lie in $U$, and all $k$-points $d_1,d_2$ of $C_2$ such that for $i=1,2$ the composite of $d_i$, $i_2$ and the projection $X\times_A k\to X$ equals $\operatorname{Spec}\pi_k$ followed by $\xi_i$, and the image of the closed point of $\operatorname{Spec} k$ under $d_i$ followed by $i_2$ is not in the range of $i_1$, then for every $Pl$-point $s$ of $D$ over $\operatorname{Spec}\rho$ for which the pull-back along $s$ of the Poincaré bundle of $D$ is isomorphic to the dual of the ideal sheaf of the graph of $\xi_1$ tensored with the ideal sheaf of the graph of $\xi_2$, and every $y\in J^0_s$ whose point $\mathrm{pts}(y)$ composed with the projection $D\times_A k\to D$ equals $\operatorname{Spec}\pi_k$ followed by $s$, the first component of $\mathrm{proj}(y)$ is zero in $J_I$.
--
--   This is the component-exchanged companion of the vanishing statement for the other component of the two-component special fibre of the Néron model of $J_1(Mp)$ at $p$: when both reductions of the $Pl$-points $\xi_1,\xi_2$ land on $C_2$ away from $C_1$, the restriction to $C_1$ of $\mathcal O(\bar\xi_1-\bar\xi_2)$ is trivial, so the $J_I$-coordinate of the reduction of the classifying point vanishes. It is used by the two existence results producing a place of $\overline{\mathbb Q}$ together with a point of $D$ whose reduction has prescribed $J_E$-class and vanishing $J_I$-coordinate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_proj_fst_eq_zero_of_points_eq_reduction_snd_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul.lean

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

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.proj_fst_eq_zero_of_points_eq_reduction_snd_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul
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

    (U : (ModularCurve.TwoChartModel A (↥K) j).Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j))]
    (hUmax : ∀ W : (ModularCurve.TwoChartModel A (↥K) j).Opens, SmoothOfRelativeDimension 1 (W.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j)) → W ≤ U)

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hπk : Function.Surjective πk) :
    ∀ (ξ₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j)) (ξ₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j))
      (d₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂) (d₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂),
      Set.range ξ₁.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) → Set.range ξ₂.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) →
      d₁.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ₁.1 →
      (d₁.1 ≫ i₂.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₁.1.base →
      d₂.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ₂.1 →
      (d₂.1 ≫ i₂.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₁.1.base →
      ∀ (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase),
        Nonempty ((hrep.some.poincare.pullbackAlong s).L ≅
          (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ξ₁.1 ξ₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ξ₂.1 ξ₂.2).idealModule) →
        ∀ (y : G.J0s),
          (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ s.1 →
          (G.proj y).1 = 0 := by sorry
