-- Prove2me | Theorems.Thm_GlobalTheory_SatMinor_isUnit_int_iff
-- name    : GlobalTheory.SatMinor.isUnit_int_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:44:57.690296+00:00
-- url     : https://prove2.me/theorems/adcdecb3-c2de-4160-9fad-13604163c737
-- title:
--   Sat Minor: is Unit int iff
-- statement:
--   The Sat Minor construction uses the is Unit int iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitMinorOfIntegralMatrix.lean#L15-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitMinorOfIntegralMatrix.lean#L15-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitMinorOfIntegralMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.SatMinor
variable {p : ℕ} [Fact p.Prime]

theorem GlobalTheory.SatMinor.isUnit_int_iff (x : PadicComplexInt p) : IsUnit x ↔ ‖(x : ℂ_[p])‖ = 1 := by sorry
