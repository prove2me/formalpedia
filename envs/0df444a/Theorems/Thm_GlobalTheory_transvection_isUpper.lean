-- Prove2me | Theorems.Thm_GlobalTheory_transvection_isUpper
-- name    : GlobalTheory.transvection_isUpper
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:54.482042+00:00
-- url     : https://prove2.me/theorems/f05b33b2-ca63-4170-8041-8637db46d789
-- title:
--   Global Theory: transvection is Upper
-- statement:
--   The Global Theory construction uses the transvection is Upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RightInvariantGLOfUpperTriangularRightInvariant.lean#L43-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RightInvariantGLOfUpperTriangularRightInvariant.lean#L43-L51

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

theorem GlobalTheory.transvection_isUpper {i j : Fin m} (hji : j < i) (x : k) :
    (transvection j i x).BlockTriangular id := by sorry
