-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_count_word_eq
-- name    : GlobalTheory.HilbFam.count_word_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:20:50.743367+00:00
-- url     : https://prove2.me/theorems/121ae6dc-e58e-4d74-8648-2fc43eed6bc8
-- title:
--   Hilb Fam: count word eq
-- statement:
--   The Hilb Fam construction uses the count word eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CountWordWithLetterMultiplicities.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CountWordWithLetterMultiplicities.lean#L10-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CountWordWithLetterMultiplicities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam

theorem GlobalTheory.HilbFam.count_word_eq (I : Type) [Fintype I] [DecidableEq I] (κ : I → ℕ) (i : I) :
    (word κ).count i = κ i := by sorry
