-- Prove2me | Theorems.Thm_GlobalTheory_NonDomZero_exists_lt_lt_of_not_antitone
-- name    : GlobalTheory.NonDomZero.exists_lt_lt_of_not_antitone
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:46:51.417552+00:00
-- url     : https://prove2.me/theorems/75cf91d0-f07b-4f21-9ecd-0903d856a6de
-- title:
--   Non Dom Zero: exists lt lt of not antitone
-- statement:
--   The Non Dom Zero construction uses the exists lt lt of not antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualWeylEqBotOfNotAntitone.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualWeylEqBotOfNotAntitone.lean#L7-L13

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualWeylEqBotOfNotAntitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NonDomZero

theorem GlobalTheory.NonDomZero.exists_lt_lt_of_not_antitone {N : ℕ} {ν : Fin N → ℕ} (hν : ¬ Antitone ν) :
    ∃ a b : Fin N, a < b ∧ ν a < ν b := by sorry
