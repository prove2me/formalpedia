-- Prove2me | Theorems.Thm_GlobalTheory_Harm_antitone_mixedWeight
-- name    : GlobalTheory.Harm.antitone_mixedWeight
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:07:14.664981+00:00
-- url     : https://prove2.me/theorems/37ad81e3-de72-5fe3-8cbc-5e9f6717cd95
-- title:
--   Harm: antitone mixed Weight
-- statement:
--   The Harm construction uses the antitone mixed Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EqZeroOfPartialSumsNonneg.lean#L115-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EqZeroOfPartialSumsNonneg.lean#L115-L128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EqZeroOfPartialSumsNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Harm
open Finset
open Finset

theorem GlobalTheory.Harm.antitone_mixedWeight (m : ℕ) {p q : ℕ} {a : Fin p → ℕ} {b : Fin q → ℕ}
    (ha : Antitone a) (hb : Antitone b) : Antitone (_root_.GlobalTheory.Harm.mixedWeight m a b) := by sorry
