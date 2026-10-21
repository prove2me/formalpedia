-- Prove2me | Theorems.Thm_MazurTransfer_original_generic_local_group_pointwise_unit_and_scalar
-- name    : MazurTransfer.original_generic_local_group_pointwise_unit_and_scalar
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T02:26:35.893874+00:00
-- url     : https://prove2.me/theorems/c1252c88-a2cb-436d-9523-793280e21c7a
-- statement:
--   For every original good-prime localization, the same selected local Picard generic group law and the same represented Picard group law have equal identity points on every original rational test scheme. All their original natural-number scalar actions are equal at every original point. The same schemes, coefficient maps, group laws and original prime hypotheses are retained. Named downstream consumer: the actual local generic point comparison and integral nineteen norm-kernel arithmetic labels.

import Definitions.Def_MazurTransfer_OriginalPicardComparisonGroupProvidersData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericGroupConstructorData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeLocalGenericGroupIdentity_generic_group_law_units_equal
import Theorems.Thm_MazurTransfer_Order13GoodPrimeGenericNormGroupLaws_generic_group_law_multiplications_equal
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison
open MazurTransfer.Order13GoodPrimeGenericNormGroupLaws

theorem MazurTransfer.original_generic_local_group_pointwise_unit_and_scalar : (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), ∀ {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ)),
(genericLocalLaw q hq).one t = (genericRepresentedLaw q hq).one t) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), ∀ {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ)) (n : ℕ)
    (x : SchemeHomOver t (localGenericPicard q hq).toBase),
(genericLocalLaw q hq).nsmul t n x = (genericRepresentedLaw q hq).nsmul t n x) := by sorry
