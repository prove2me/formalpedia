-- Prove2me | Theorems.Thm_GlobalTheory_MinorInt_weight_le
-- name    : GlobalTheory.MinorInt.weight_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:25:26.780298+00:00
-- url     : https://prove2.me/theorems/42b471b2-6eaf-4f7f-838c-17380b287430
-- title:
--   Minor Int: weight le
-- statement:
--   The Minor Int construction uses the weight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L255-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L255-L264

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder
open GlobalTheory GlobalTheory.MinorInt

theorem GlobalTheory.MinorInt.weight_le {s u M : ℝ} (hs : 0 < s) (h : 1 / 2 ≤ s ^ 2 * u) (hM : u ≤ M) (p q k : ℕ) :
    s ^ (2 * q) * (s ^ (2 * (p + q) + k))⁻¹ ≤ (2 * u) ^ p * (1 + 2 * M) ^ k := by sorry
