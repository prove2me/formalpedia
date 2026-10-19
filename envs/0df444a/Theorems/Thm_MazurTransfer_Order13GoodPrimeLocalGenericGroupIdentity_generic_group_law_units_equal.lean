-- Prove2me | Theorems.Thm_MazurTransfer_Order13GoodPrimeLocalGenericGroupIdentity_generic_group_law_units_equal
-- name    : MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity.generic_group_law_units_equal
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T04:29:04.746757+00:00
-- url     : https://prove2.me/theorems/0013e65d-86ab-4d22-b3d5-c39fe0f5f6a8
-- title:
--   The two generic Picard group laws have the same unit
-- statement:
--   Let $q$ be a prime with $q \nmid 104$. On the generic fibre of the selected local integral Picard model, consider the group law obtained by base changing the integral Picard group law and the group law coming from its literal rational Picard representation. Their unit sections agree:
--
--   $$e_{\mathrm{generic\ local}}=e_{\mathrm{represented}}.$$
--
--   This supplies the zero-section compatibility needed for comparing the multiplication maps and transporting the actual nineteen-norm group laws.
-- source:
--   MazurTheorem, Order13GoodPrimeLocalGenericGroupIdentity.lean, complete original theorem and hypotheses, source SHA-256 5c0c699cd69d6ccc6911562bc192066a0478176f2835da167376e0bea205cde2, Apache-2.0. Official Anthropic FLT at https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 .

import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericGroupConstructorData
open CategoryTheory CategoryTheory.Limits
open MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity

theorem MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity.generic_group_law_units_equal (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) :
    (genericLocalLaw q hq).one (𝟙 _) =
      (genericRepresentedLaw q hq).one (𝟙 _) := by sorry
