-- Prove2me | Theorems.Thm_GlobalTheory_upperFactor_det
-- name    : GlobalTheory.upperFactor_det
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:24:35.599156+00:00
-- url     : https://prove2.me/theorems/88040ffd-48ad-4ed9-9f5c-1ecba4f4c78a
-- title:
--   Global Theory: upper Factor det
-- statement:
--   The Global Theory construction uses the upper Factor det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RightInvariantGLOfUpperTriangularRightInvariant.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RightInvariantGLOfUpperTriangularRightInvariant.lean#L57-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightInvariantGLOfUpperTriangularRightInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory
variable {k : Type} [Field k] {m : ℕ}

theorem GlobalTheory.upperFactor_det {i j : Fin m} (hji : j < i) {x : k} (hx : x ≠ 0) :
    (upperFactor i j x).det = -1 := by sorry
