-- Prove2me | Theorems.Thm_GlobalTheory_loweringWord_zero_or_pos
-- name    : GlobalTheory.loweringWord_zero_or_pos
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:10:44.149121+00:00
-- url     : https://prove2.me/theorems/65b4157f-b417-463d-a962-50cff612fd26
-- title:
--   Global Theory: lowering Word zero or pos
-- statement:
--   The Global Theory construction uses the lowering Word zero or pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsStableSubmoduleTopWeightLine.lean#L85-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsStableSubmoduleTopWeightLine.lean#L85-L92

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsStableSubmoduleTopWeightLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open GlobalTheory
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
  {E : Fin n → Fin n → Module.End ℂ V} {ν : Fin n → ℂ} {v : V}

theorem GlobalTheory.loweringWord_zero_or_pos {N : ℕ} {x : V} (hx : LoweringWord E v N x) :
    x = v ∨ 0 < N := by sorry
