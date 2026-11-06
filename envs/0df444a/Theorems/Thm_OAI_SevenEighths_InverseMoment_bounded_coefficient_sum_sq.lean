-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_bounded_coefficient_sum_sq
-- name    : OAI.SevenEighths.InverseMoment.bounded_coefficient_sum_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:25:52.40814+00:00
-- url     : https://prove2.me/theorems/4c332a32-0a91-442a-b4f3-c81928717570
-- title:
--   Inverse Moment: bounded coefficient sum sq
-- statement:
--   The Inverse Moment construction uses the bounded coefficient sum sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/SieveComposition.lean#L20-L24
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/SieveComposition.lean#L20-L24

import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Fibers
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_SieveComposition
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section

theorem OAI.SevenEighths.InverseMoment.bounded_coefficient_sum_sq {C : Type*} [Fintype C]
    (b f : C → ℂ) (hb : ∀ c, ‖b c‖ ≤ 1) :
    ‖∑ c, b c * f c‖ ^ 2 ≤ (Fintype.card C : ℝ) * ∑ c, ‖f c‖ ^ 2 := by sorry
