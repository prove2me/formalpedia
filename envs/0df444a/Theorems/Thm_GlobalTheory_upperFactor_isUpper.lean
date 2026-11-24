-- Prove2me | Theorems.Thm_GlobalTheory_upperFactor_isUpper
-- name    : GlobalTheory.upperFactor_isUpper
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:24:32.158972+00:00
-- url     : https://prove2.me/theorems/1d446e7b-8e36-4c68-922c-3f25b5e0af36
-- title:
--   Global Theory: upper Factor is Upper
-- statement:
--   The Global Theory construction uses the upper Factor is Upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RightInvariantGLOfUpperTriangularRightInvariant.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RightInvariantGLOfUpperTriangularRightInvariant.lean#L53-L55

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

theorem GlobalTheory.upperFactor_isUpper {i j : Fin m} (hji : j < i) (x : k) :
    (upperFactor i j x).BlockTriangular id := by sorry
