-- Prove2me | Theorems.Thm_GlobalTheory_T_integralGLSet_isOpen_and_isCompact
-- name    : GlobalTheory.T.integralGLSet_isOpen_and_isCompact
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:34:11.914522+00:00
-- url     : https://prove2.me/theorems/88a7b0d6-bde5-4d1e-92c9-825b70c61024
-- title:
--   T: integral GLSet is Open and is Compact
-- statement:
--   The T construction uses the integral GLSet is Open and is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralGLSetIsOpenAndIsCompactStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralGLSetIsOpenAndIsCompactStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralGLSetIsOpenAndIsCompact
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralGLSetIsOpenAndIsCompactStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.integralGLSet_isOpen_and_isCompact : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [ProperSpace F] (n : ℕ), IsOpen (glO n F) ∧ IsCompact (glO n F) := by sorry
