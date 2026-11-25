-- Prove2me | Theorems.Thm_GlobalTheory_encard_eq_tsum_fibers
-- name    : GlobalTheory.encard_eq_tsum_fibers
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:49:31.747222+00:00
-- url     : https://prove2.me/theorems/201eeaed-511d-483e-84cf-ca0735aca9dc
-- title:
--   Global Theory: encard eq tsum fibers
-- statement:
--   The Global Theory construction uses the encard eq tsum fibers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TsumInvStabilizerEqTsumMulFiber.lean#L58-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TsumInvStabilizerEqTsumMulFiber.lean#L58-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TsumInvStabilizerEqTsumMulFiber
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ENNReal
open GlobalTheory
open MulAction

theorem GlobalTheory.encard_eq_tsum_fibers {L Q : Type} (F : Set L) (q : L → Q) :
    (F.encard : ℝ≥0∞) = ∑' o : Q, (({z | z ∈ F ∧ q z = o}).encard : ℝ≥0∞) := by sorry
