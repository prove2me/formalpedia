-- Prove2me | Theorems.Thm_MazurTransfer_original_integral_generic_point_comparison_laws
-- name    : MazurTransfer.original_integral_generic_point_comparison_laws
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T02:38:39.950983+00:00
-- url     : https://prove2.me/theorems/e215777c-1acb-41bc-9f68-08733f444fa5
-- statement:
--   For every original good-prime localization, the same selected integral Picard model and the same actual rational Picard have their original equivalence of points over every original rational test scheme. This map preserves the original identity and multiplication, commutes with every original test-scheme precomposition, and respects the same chosen integral extension of every original rational endomorphism. All original schemes, maps, group structures, prime and coefficient hypotheses are retained. Named downstream consumer: the actual arithmetic field-point and norm-kernel Galois comparison.

import Definitions.Def_MazurTransfer_OriginalIntegralGenericPointComparisonData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Theorems.Thm_MazurTransfer_original_picard_comparison_group_compatibility
import Theorems.Thm_MazurTransfer_original_generic_local_group_pointwise_unit_and_scalar
import Theorems.Thm_MazurTransfer_Order13GoodPrimeGenericNormGroupLaws_generic_group_law_multiplications_equal
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard GoodReductionJacobian NeronModelInfra
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13GoodPrimeLocalPicardModels MazurTransfer.Order13LocalIntegralCoefficientMaps
open MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison MazurTransfer.Order13GoodPrimeIntegralNormExtensions
open MazurTransfer.Order13IntegralGenericPointComparison
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13IntegralGenericPointComparison.instGrpObjOverSchemeSpecOfRatMkToBaseLocalGenericPicard_order13IntegralGenericPointComparison
attribute [local instance] MazurTransfer.Order13IntegralGenericPointComparison.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralGenericPointComparison

theorem MazurTransfer.original_integral_generic_point_comparison_laws : (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ)),
actualToLocal q hq (1 : Over.mk t ⟶ Over.mk actualPicard.toBase) =
      (localLaw q hq).one (t ≫ localGenericInclusion q)) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ))
    (a b : Over.mk t ⟶ Over.mk actualPicard.toBase),
actualToLocal q hq (a * b) = (localLaw q hq).mul (t ≫ localGenericInclusion q)
      (actualToLocal q hq a) (actualToLocal q hq b)) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), ∀ {T T' : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ))
    (t' : T' ⟶ Spec (CommRingCat.of ℚ)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (a : Over.mk t ⟶ Over.mk actualPicard.toBase),
actualToLocal q hq ((Over.homMk ψ hψ : Over.mk t' ⟶ Over.mk t) ≫ a) =
      GoodReductionJacobian.schemeHomOverComp ψ (by rw [← Category.assoc, hψ])
        (actualToLocal q hq a)) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), ∀ {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ))
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (x : SchemeHomOver t (localGenericPicard q hq).toBase),
RelativeGroupLaw.baseChangePointToBase (f := (localPicard q hq).toBase)
      (localGenericInclusion q) (NeronModelInfra.schemeHomOverComp x (localGenericNorm q hq φ)) =
      NeronModelInfra.schemeHomOverComp
        (RelativeGroupLaw.baseChangePointToBase (f := (localPicard q hq).toBase)
          (localGenericInclusion q) x) (integralNorm q hq φ)) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ))
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (a : Over.mk t ⟶ Over.mk actualPicard.toBase),
actualToLocal q hq (a ≫ φ) =
      NeronModelInfra.schemeHomOverComp (actualToLocal q hq a) (integralNorm q hq φ)) := by sorry
