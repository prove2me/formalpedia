-- Prove2me | Theorems.Thm_GlobalTheory_CharFamily_one_add_pow_le
-- name    : GlobalTheory.CharFamily.one_add_pow_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:07:56.959122+00:00
-- url     : https://prove2.me/theorems/73b7a739-c3d2-4aab-bddb-a600c156f124
-- title:
--   Char Family: one add pow le
-- statement:
--   The Char Family construction uses the one add pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzFamilyPhaseBound.lean#L114-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzFamilyPhaseBound.lean#L114-L121

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

theorem GlobalTheory.CharFamily.one_add_pow_le (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : (1 + a) ^ n ≤ 2 ^ n * (1 + a ^ n) := by sorry
