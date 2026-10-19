-- Prove2me | Theorems.Thm_MazurTransfer_Order13GoodPrimeGenericNormGroupLaws_generic_group_law_multiplications_equal
-- name    : MazurTransfer.Order13GoodPrimeGenericNormGroupLaws.generic_group_law_multiplications_equal
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T04:50:00.212342+00:00
-- url     : https://prove2.me/theorems/a21b998c-7e21-4972-a0a6-ca0dd20c1754
-- title:
--   The generic local and represented Picard multiplication laws agree
-- statement:
--   Let $q$ be a prime with $q \nmid 104$. On the generic fibre of the selected local Picard model, let $G_{\mathrm{loc}}$ be the base change of its integral group law and let $G_{\mathrm{rep}}$ be the law obtained from its literal rational Picard representation. For every scheme $T$ over $\mathbb Q$ and every pair of $T$-points $x,y$,
--
--   $$x+_{G_{\mathrm{loc}}}y=x+_{G_{\mathrm{rep}}}y.$$
--
--   This identifies the multiplication operations on the same underlying generic Picard scheme, which is needed to compare actual rational norm maps with integral multiplication by nineteen.
-- source:
--   MazurTheorem, Order13GoodPrimeGenericNormGroupLaws.lean, complete original theorem and hypotheses, full source SHA-256 27a46b8447e29fb75044ed0da6160be98e53de8d0288f9d1da7231ff39f9705d, Apache-2.0. Official Anthropic FLT interfaces at https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 .

import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericGroupConstructorData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeLocalGenericGroupIdentity_generic_group_law_units_equal
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalGenericGroupIdentity Order13GoodPrimeLocalGenericPicardComparison

theorem MazurTransfer.Order13GoodPrimeGenericNormGroupLaws.generic_group_law_multiplications_equal (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ))
    (x y : SchemeHomOver t (localGenericPicard q hq).toBase) :
    (genericLocalLaw q hq).mul t x y = (genericRepresentedLaw q hq).mul t x y := by sorry
