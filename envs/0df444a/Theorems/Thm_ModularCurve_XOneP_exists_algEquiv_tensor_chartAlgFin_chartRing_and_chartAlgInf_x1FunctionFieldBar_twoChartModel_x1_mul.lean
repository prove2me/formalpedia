-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_algEquiv_tensor_chartAlgFin_chartRing_and_chartAlgInf_x1FunctionFieldBar_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_algEquiv_tensor_chartAlgFin_chartRing_and_chartAlgInf_x1FunctionFieldBar_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/ea7df03e-26a5-5dd4-b349-e2adb5d9caa6
-- title:
--   Geometric base change of the two chart algebras of X₁(Mp)
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$, let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $p$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L \subseteq L((q))$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield of $L((q))$ generated over $L$ by the coefficientwise images of the $q$-expansion field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) attached to $\Gamma_1(Mp)$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A \to L$, with $K$ an $A$-algebra compatibly with $A \to L \to K$. Let $j \in K$ be the element whose Laurent series is the coefficientwise image in $L((q))$ of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) $= q^{-1}\cdot(\text{the rational power series } jNumQ)$, and assume $j \ne 0$. Fix algebra maps $A \to \overline{\mathbb{Q}}$ and $L \to \overline{\mathbb{Q}}$ forming a scalar tower, where $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Let $jb$ be the element of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) $=$ `laurentBaseChange (AlgebraicClosure ℚ) (x1FunctionField (M * p))` whose Laurent series is the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) in $\overline{\mathbb{Q}}((q))$, and assume $jb \ne 0$. Finally assume `hmem`: pushing the coefficients of every element of $K$ along $L \to \overline{\mathbb{Q}}$ lands in [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182). The conclusion asserts two things. First, there is an isomorphism of $\overline{\mathbb{Q}}$-algebras $eFin$ from $\overline{\mathbb{Q}} \otimes_A$ [`ModularCurve.TwoChart.chartAlgFin A K j`](def/ModularCurve_TwoChartModel.html#L135) — the tensor product with the $A$-subalgebra of $K$ of elements integral over $A[j]$ — onto [`AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) {jb}`](def/JacJ1_ChartAlgebra.html#L45), the $\overline{\mathbb{Q}}$-subalgebra of `x1FunctionFieldBar (M * p)` of elements integral over $\overline{\mathbb{Q}}[jb]$, such that for every $b$ in the source subalgebra, $eFin(1 \otimes b)$ is, as an element of `x1FunctionFieldBar (M * p)`, the coefficientwise image of the Laurent series of $b$ along $L \to \overline{\mathbb{Q}}$. Second, the same statement with $j$ replaced by $j^{-1}$ and $jb$ by $jb^{-1}$, i.e. an isomorphism $eInf$ from $\overline{\mathbb{Q}} \otimes_A$ `chartAlgInf A K j` onto `chartRing (AlgebraicClosure ℚ) {jb⁻¹}` acting the same way on elements $1 \otimes b$.
--
--   The statement identifies the geometric base change to $\overline{\mathbb{Q}}$ of the two chart algebras (normalisations of $A[j]$ and $A[j^{-1}]$ in the $q$-expansion field) of the two-chart integral model of $X_1(Mp)$ over $A = \mathbb{Z}_{(p)}[\zeta_p]$ with the corresponding chart rings of $\overline{\mathbb{Q}}(X_1(Mp))$, compatibly with coefficientwise extension of $q$-expansions. The two isomorphisms are the inputs to the glueing construction comparing a smooth proper model of $\overline{\mathbb{Q}}(X_1(Mp))$ with the geometric generic fibre of the two-chart model, and are used in the identification of points with places and in the computations of the Galois and diamond actions on that model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_algEquiv_tensor_chartAlgFin_chartRing_and_chartAlgInf_x1FunctionFieldBar_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open scoped TensorProduct

theorem ModularCurve.XOneP.exists_algEquiv_tensor_chartAlgFin_chartRing_and_chartAlgInf_x1FunctionFieldBar_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]
    (jb : ↥(ModularCurve.x1FunctionFieldBar (M * p)))
    (hjb : (jb : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq) [Fact (jb ≠ 0)]
    (hmem : ∀ b : ↥K, ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) ∈ ModularCurve.x1FunctionFieldBar (M * p)) :
    (∃ eFin : (AlgebraicClosure ℚ) ⊗[A] ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)
        ≃ₐ[AlgebraicClosure ℚ] ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(ModularCurve.x1FunctionFieldBar (M * p)))),
      ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        ((eFin ((1 : AlgebraicClosure ℚ) ⊗ₜ[A] b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(ModularCurve.x1FunctionFieldBar (M * p))))) : ↥(ModularCurve.x1FunctionFieldBar (M * p))) =
          ⟨ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L), hmem b⟩) ∧
    (∃ eInf : (AlgebraicClosure ℚ) ⊗[A] ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j)
        ≃ₐ[AlgebraicClosure ℚ] ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(ModularCurve.x1FunctionFieldBar (M * p)))),
      ∀ b : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j),
        ((eInf ((1 : AlgebraicClosure ℚ) ⊗ₜ[A] b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(ModularCurve.x1FunctionFieldBar (M * p))))) : ↥(ModularCurve.x1FunctionFieldBar (M * p))) =
          ⟨ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L), hmem b⟩) := by sorry
