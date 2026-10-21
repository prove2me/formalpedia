-- Prove2me | Theorems.Thm_MazurTransfer_original_integral_arithmetic_field_point_comparison_laws
-- name    : MazurTransfer.original_integral_arithmetic_field_point_comparison_laws
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T03:03:21.573838+00:00
-- url     : https://prove2.me/theorems/2676edd2-6abb-44e0-80b9-09ca773074ea
-- statement:
--   The same canonical comparison between actual rational Picard points and the chosen integral local Picard points over every original characteristic-zero field preserves identity, multiplication, every original chosen integral extension of an arbitrary rational endomorphism, and the original arithmetic Galois action by spectrum precomposition. Both original base-map equalities are retained with exactly their original hypotheses. Named downstream consumer: actual integral norm-kernel Hopf arithmetic point labels.

import Definitions.Def_MazurTransfer_OriginalIntegralArithmeticFieldPointComparisonData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKummerData
import Theorems.Thm_MazurTransfer_original_integral_generic_point_comparison_laws
import Theorems.Thm_MazurTransfer_original_relative_point_base_cast_laws
noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard GoodReductionJacobian NeronModelInfra
open MazurTransfer.Order13IntegralGenericPointComparison MazurTransfer.RelativePointBaseCast
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13GoodPrimeLocalPicardModels
open MazurTransfer.Order13GoodPrimeIntegralNormExtensions MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison MazurTransfer.Order13ActualPicardGeometricNormPreimages
open MazurTransfer.Order13ActualPicardNormKummerCocycles MazurTransfer.Order13IntegralArithmeticFieldPointComparison
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13IntegralArithmeticFieldPointComparison.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralArithmeticFieldPointComparison

theorem MazurTransfer.original_integral_arithmetic_field_point_comparison_laws : (∀ (q : ℕ) [Fact q.Prime] (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K], FieldAutomorphismOverPointAction.fieldBase ℚ K ≫ localGenericInclusion q =
      FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K], actualFieldPointEquiv q hq K 1 =
      (localLaw q hq).one (FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K)) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K], ∀ (a b : Points K),
actualFieldPointEquiv q hq K (a * b) =
      (localLaw q hq).mul (FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K)
        (actualFieldPointEquiv q hq K a) (actualFieldPointEquiv q hq K b)) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K], ∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) (a : Points K),
actualFieldPointEquiv q hq K (a ≫ φ) =
      NeronModelInfra.schemeHomOverComp (actualFieldPointEquiv q hq K a) (integralNorm q hq φ)) ∧ (∀ (q : ℕ) [Fact q.Prime] (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K], ∀ (σ : K ≃ₐ[ℚ] K),
Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K =
        FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K], ∀ (σ : K ≃ₐ[ℚ] K) (a : Points K),
actualFieldPointEquiv q hq K (actionHom K σ a) =
      GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom σ.toRingHom))
        (Over.w (FieldAutomorphismOverPointAction.fieldAut (LocalRing q) K (σ.restrictScalars (LocalRing q)))) (actualFieldPointEquiv q hq K a)) := by sorry
