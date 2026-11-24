-- Prove2me | Theorems.Thm_GlobalTheory_CharFamily_contDiff_char
-- name    : GlobalTheory.CharFamily.contDiff_char
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:08:00.052487+00:00
-- url     : https://prove2.me/theorems/d32f8b93-4c33-4bc8-9cb0-7db61d97c8f7
-- title:
--   Char Family: cont Diff char
-- statement:
--   The Char Family construction uses the cont Diff char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzFamilyPhaseBound.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzFamilyPhaseBound.lean#L54-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFamilyPhaseBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
open GlobalTheory GlobalTheory.CharFamily
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem GlobalTheory.CharFamily.contDiff_char (L : E →L[ℝ] ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : E => Complex.exp (I * (L x : ℂ))) := by sorry
