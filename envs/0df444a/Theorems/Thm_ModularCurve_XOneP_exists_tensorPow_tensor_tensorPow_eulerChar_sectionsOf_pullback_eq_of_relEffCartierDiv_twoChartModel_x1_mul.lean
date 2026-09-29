-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_tensorPow_tensor_tensorPow_eulerChar_sectionsOf_pullback_eq_of_relEffCartierDiv_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_tensorPow_tensor_tensorPow_eulerChar_sectionsOf_pullback_eq_of_relEffCartierDiv_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/cb35ee3b-a1c6-5ec8-896e-530a644f1181
-- title:
--   Bidegree-zero twist of L̄^{⊗ n} on the special fibre
-- statement:
--   Fix a prime $p$, an integer $M\ge 5$ with $p\nmid M$, a field $L$ of characteristic zero which is a $\{p\}$-cyclotomic extension of $\mathbb Q$, a primitive $p$-th root of unity $\zeta\in L$, and let $K$ be the intermediate field of $L\subset\mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the image under coefficientwise extension of scalars of the function field $\mathbb Q$-algebra of $X_1(Mp)$. Let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal and $\zeta$ in the image of $A$, acting on $K$ compatibly, and let $j\in K$, $j\neq 0$, correspond to the $q$-expansion of the modular function $j$. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$, let $C_1,C_2$ be proper, smooth of relative dimension $1$, geometrically integral and integral $k$-schemes, and let $i_1,i_2$ be closed immersions over $k$ of $C_1,C_2$ into the fibre $X_k$ of the two-chart model $\mathrm{modelTo}\,A\,K\,j$ along $A\to k$, whose images jointly cover $X_k$, with $C_1\times_{X_k}C_2$ reduced and of cardinality $n>0$; $n$ distinct $k$-points $z_i$ of this intersection, sections over $C_1$ and $C_2$, are given. Further data: a section $\varepsilon$ of the model over $\operatorname{Spec}A$, a relative $\mathrm{Pic}^0$ designation $D$ together with a representability datum for the subcondition of fibrewise algebraic equivalence to zero, properness of the model, a discrete valuation domain $O$ with a map $\rho_O\colon A\to O$ carrying the maximal ideal of $A$ onto that of $O$ and a map $O\to k$ compatible with $A\to k$, and a base-change morphism $bc$ from $X_k$ to $X_O$ commuting with both projections up to $\operatorname{Spec}(O\to k)$. Finally, for some $r$, let $\bar E_1,\bar E_2$ be relative effective Cartier divisors of fibre rank $r$ on the model relative to $\operatorname{Spec}O$, whose ideal sheaves are invertible and remain invertible after pulling back along $bc$, $i_1\circ bc$ and $i_2\circ bc$, with the $bc$-pullback cut out finitely over $\operatorname{Spec}k$, and let $\mathcal V,\mathcal V_1,\mathcal V_2$ be two-affine-open covers of $X_k$, $C_1$, $C_2$. The conclusion asserts the existence of $d\in\mathbb N$ and of modules $B,N$ on $X_O$ with $B$ either the module of the kernel ideal sheaf of $i_2\circ bc$ or its dual, with $N=(\bar E_1.\mathrm{lineBundle}\otimes\bar E_2.\mathrm{idealModule})^{\otimes n}\otimes B^{\otimes d}$ (that is, the $n$-th tensor power of the dual of the ideal module of $\bar E_1$ tensored with the ideal module of $\bar E_2$, twisted by $B^{\otimes d}$), such that $N$ is invertible and, for $\nu=1,2$, the difference $\dim_k H^0-\dim_k H^1$ of the two-chart Čech complex of the pullback of $N$ along $bc$ and then $i_\nu$ on $C_\nu$ equals the same difference for the unit module on $C_\nu$.
--
--   This is the bidegree bookkeeping step in the line-bundle extension argument on the two-chart regular model of $X_1(Mp)$ over an unramified discrete valuation ring: after twisting $\bar{\mathcal L}^{\otimes n}=(\mathcal O(\bar E_1)\otimes I(\bar E_2))^{\otimes n}$ by a power of the ideal module of one component (or its dual), the resulting invertible module has the Euler characteristic of the structure sheaf on each of the two components of the special fibre, i.e. bidegree $(0,0)$. It is used in the construction of a rigidified line bundle which is fibrewise algebraically equivalent to zero and pulls back from a tensor power of the Poincaré bundle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_tensorPow_tensor_tensorPow_eulerChar_sectionsOf_pullback_eq_of_relEffCartierDiv_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.exists_tensorPow_tensor_tensorPow_eulerChar_sectionsOf_pullback_eq_of_relEffCartierDiv_twoChartModel_x1_mul
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
    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ρO : A →+* O) (hunr : Ideal.map ρO (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal O)
    (toκ : O →+* k) (htoκ : toκ.comp ρO = algebraMap A k)
    (bc : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ))

    (z : Fin n → (Spec (CommRingCat.of k) ⟶ pullback i₁.1 i₂.1))
    (hz₁ : ∀ i, (z i ≫ pullback.fst i₁.1 i₂.1) ≫ c₁ = 𝟙 _) (hz₂ : ∀ i, (z i ≫ pullback.snd i₁.1 i₂.1) ≫ c₂ = 𝟙 _)
    (hzinj : Function.Injective fun i => (z i).base (IsLocalRing.closedPoint k))
    [IsIntegral C₁] [IsIntegral C₂]

    (r : ℕ) (Ē₁ Ē₂ : RelEffCartierDiv (ModularCurve.TwoChart.modelTo A (↥K) j) r (Spec.map (CommRingCat.ofHom ρO)))
    (hĒ₁ : Ē₁.I.IsInvertible) (hĒ₁bc : (Ē₁.I.comap bc).IsInvertible)
    (hĒ₁₁ : (Ē₁.I.comap (i₁.1 ≫ bc)).IsInvertible) (hĒ₁₂ : (Ē₁.I.comap (i₂.1 ≫ bc)).IsInvertible)
    (hĒ₁fin : IsFinite ((Ē₁.I.comap bc).subschemeι ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
    (hĒ₂ : Ē₂.I.IsInvertible) (hĒ₂bc : (Ē₂.I.comap bc).IsInvertible)
    (hĒ₂₁ : (Ē₂.I.comap (i₁.1 ≫ bc)).IsInvertible) (hĒ₂₂ : (Ē₂.I.comap (i₂.1 ≫ bc)).IsInvertible)
    (hĒ₂fin : IsFinite ((Ē₂.I.comap bc).subschemeι ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))

    (𝒱 : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).TwoAffineOpenCover)
    (𝒱₁ : C₁.TwoAffineOpenCover) (𝒱₂ : C₂.TwoAffineOpenCover) :
    ∃ (d : ℕ) (B N : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))).Modules),
      (B = ((i₂.1 ≫ bc).ker).module ∨ B = ((i₂.1 ≫ bc).ker).invModule) ∧
      N = (Ē₁.lineBundle ⊗ Ē₂.idealModule).tensorPow n ⊗ B.tensorPow d ∧
      Scheme.Modules.IsInvertible N ∧
      (Module.finrank k (𝒱₁.sectionsOf c₁ ((Scheme.Modules.pullback i₁.1).obj ((Scheme.Modules.pullback bc).obj N))).H0 : ℤ) -
          Module.finrank k (𝒱₁.sectionsOf c₁ ((Scheme.Modules.pullback i₁.1).obj ((Scheme.Modules.pullback bc).obj N))).H1 =
        (Module.finrank k (𝒱₁.sectionsOf c₁ (SheafOfModules.unit C₁.ringCatSheaf : C₁.Modules)).H0 : ℤ) -
          Module.finrank k (𝒱₁.sectionsOf c₁ (SheafOfModules.unit C₁.ringCatSheaf : C₁.Modules)).H1 ∧
      (Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj ((Scheme.Modules.pullback bc).obj N))).H0 : ℤ) -
          Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj ((Scheme.Modules.pullback bc).obj N))).H1 =
        (Module.finrank k (𝒱₂.sectionsOf c₂ (SheafOfModules.unit C₂.ringCatSheaf : C₂.Modules)).H0 : ℤ) -
          Module.finrank k (𝒱₂.sectionsOf c₂ (SheafOfModules.unit C₂.ringCatSheaf : C₂.Modules)).H1 := by sorry
