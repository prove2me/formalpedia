-- Prove2me | Theorems.Thm_GlobalTheory_two_mul_evenDefectTriangle
-- name    : GlobalTheory.two_mul_evenDefectTriangle
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:20.957169+00:00
-- url     : https://prove2.me/theorems/3ad29220-b5af-4cb5-8b3c-78f855ddc028
-- title:
--   Global Theory: two mul even Defect Triangle
-- statement:
--   The Global Theory construction uses the two mul even Defect Triangle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CubicalFunctionOfHomomorphism.lean#L7-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CubicalFunctionOfHomomorphism.lean#L7-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CubicalFunctionOfHomomorphism
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.two_mul_evenDefectTriangle (n : ℤ) : 2 * evenDefectTriangle n = n * (n - 1) := by sorry
