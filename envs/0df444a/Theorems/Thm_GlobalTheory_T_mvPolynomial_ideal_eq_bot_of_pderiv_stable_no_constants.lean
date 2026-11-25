-- Prove2me | Theorems.Thm_GlobalTheory_T_mvPolynomial_ideal_eq_bot_of_pderiv_stable_no_constants
-- name    : GlobalTheory.T.mvPolynomial_ideal_eq_bot_of_pderiv_stable_no_constants
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:36:09.605164+00:00
-- url     : https://prove2.me/theorems/e1fa0d42-8703-52fd-9352-10069eb11813
-- title:
--   T: mv Polynomial ideal eq bot of pderiv stable no constants
-- statement:
--   The T construction uses the mv Polynomial ideal eq bot of pderiv stable no constants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MvPolynomialIdealEqBotOfPderivStableNoConstantsStatement.lean#L5-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MvPolynomialIdealEqBotOfPderivStableNoConstantsStatement.lean#L5-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialIdealEqBotOfPderivStableNoConstants
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialIdealEqBotOfPderivStableNoConstantsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mvPolynomial_ideal_eq_bot_of_pderiv_stable_no_constants : ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (r : ℕ)
    (I : Ideal (MvPolynomial (Fin r) R)),
  (∀ P ∈ I, ∀ i, MvPolynomial.pderiv i P ∈ I) → (∀ a : R, MvPolynomial.C a ∈ I → a = 0) → I = ⊥ := by sorry
