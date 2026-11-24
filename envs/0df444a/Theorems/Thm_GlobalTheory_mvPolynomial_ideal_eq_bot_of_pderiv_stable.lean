-- Prove2me | Theorems.Thm_GlobalTheory_mvPolynomial_ideal_eq_bot_of_pderiv_stable
-- name    : GlobalTheory.mvPolynomial_ideal_eq_bot_of_pderiv_stable
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:12:20.964798+00:00
-- url     : https://prove2.me/theorems/2aca58af-153d-4e04-a629-3c4ce1a4097b
-- title:
--   Global Theory: mv Polynomial ideal eq bot of pderiv stable
-- statement:
--   The Global Theory construction uses the mv Polynomial ideal eq bot of pderiv stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MvPolynomialIdealEqBotOfPderivStableNoConstants.lean#L7-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MvPolynomialIdealEqBotOfPderivStableNoConstants.lean#L7-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialIdealEqBotOfPderivStableNoConstants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial Finsupp

theorem GlobalTheory.mvPolynomial_ideal_eq_bot_of_pderiv_stable :
    ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (r : ℕ)
    (I : Ideal (MvPolynomial (Fin r) R)),
  (∀ P ∈ I, ∀ i, MvPolynomial.pderiv i P ∈ I) → (∀ a : R, MvPolynomial.C a ∈ I → a = 0) → I = ⊥ := by sorry
