-- Prove2me | Theorems.Thm_GlobalTheory_SatMinor_mem_int_iff
-- name    : GlobalTheory.SatMinor.mem_int_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:44.812437+00:00
-- url     : https://prove2.me/theorems/effbbd06-674a-45c2-af8f-3fb35b965444
-- title:
--   Sat Minor: mem int iff
-- statement:
--   The Sat Minor construction uses the mem int iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitMinorOfIntegralMatrix.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitMinorOfIntegralMatrix.lean#L9-L13

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

theorem GlobalTheory.SatMinor.mem_int_iff (x : ℂ_[p]) : x ∈ PadicComplexInt p ↔ ‖x‖ ≤ 1 := by sorry
