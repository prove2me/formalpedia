-- Prove2me | Theorems.Thm_GlobalTheory_T_qminor_commute_of_commute_columns
-- name    : GlobalTheory.T.qminor_commute_of_commute_columns
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:36:45.306736+00:00
-- url     : https://prove2.me/theorems/82398e2e-4528-5c6e-9ade-43a36bc8558c
-- title:
--   T: qminor commute of commute columns
-- statement:
--   The T construction uses the qminor commute of commute columns property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/QminorCommOfCommColumnsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/QminorCommOfCommColumnsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QminorCommOfCommColumns
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QminorCommOfCommColumnsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.qminor_commute_of_commute_columns : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (x : A) (a b : Fin t → Fin n) (u : ℂ), (∀ (c : Fin n) (i : Fin t), E c (b i) * x = x * E c (b i)) → qminor E a b u * x = x * qminor E a b u := by sorry
