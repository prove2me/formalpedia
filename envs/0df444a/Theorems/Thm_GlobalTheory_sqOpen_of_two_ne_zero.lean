-- Prove2me | Theorems.Thm_GlobalTheory_sqOpen_of_two_ne_zero
-- name    : GlobalTheory.sqOpen_of_two_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:22.341452+00:00
-- url     : https://prove2.me/theorems/aacba231-3e15-4214-bb1f-078b870bf27f
-- title:
--   Global Theory: sq Open of two ne zero
-- statement:
--   The Global Theory construction uses the sq Open of two ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SquaringOpenAtOneOfCompleteTwoNeZero.lean#L8-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SquaringOpenAtOneOfCompleteTwoNeZero.lean#L8-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquaringOpenAtOneOfCompleteTwoNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
open GlobalTheory

theorem GlobalTheory.sqOpen_of_two_ne_zero : ∀ (K : Type) [NormedField K] [CompleteSpace K], (2 : K) ≠ 0 → SqOpen K := by sorry
