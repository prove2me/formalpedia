-- Prove2me | Theorems.Thm_GlobalTheory_commute_of_commute_separable_charpoly
-- name    : GlobalTheory.commute_of_commute_separable_charpoly
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:11:18.064966+00:00
-- url     : https://prove2.me/theorems/065d9395-2f92-43ab-839f-679e5da81914
-- title:
--   Global Theory: commute of commute separable charpoly
-- statement:
--   The Global Theory construction uses the commute of commute separable charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CommuteOfCommuteSeparableCharpoly.lean#L95-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CommuteOfCommuteSeparableCharpoly.lean#L95-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommuteOfCommuteSeparableCharpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory
open Matrix Polynomial

theorem GlobalTheory.commute_of_commute_separable_charpoly :
    ∀ (K : Type) [Field K] (n : ℕ) (y a b : Matrix (Fin n) (Fin n) K), y.charpoly.Separable →
      a * y = y * a → b * y = y * b → a * b = b * a := by sorry
