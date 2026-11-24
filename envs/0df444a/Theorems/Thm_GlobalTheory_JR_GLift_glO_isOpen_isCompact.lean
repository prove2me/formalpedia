-- Prove2me | Theorems.Thm_GlobalTheory_JR_GLift_glO_isOpen_isCompact
-- name    : GlobalTheory.JR.GLift.glO_isOpen_isCompact
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:32:18.86386+00:00
-- url     : https://prove2.me/theorems/7a89a8f3-bbfe-4a01-9e46-30b204825dca
-- title:
--   GLift: gl O is Open is Compact
-- statement:
--   The GLift construction uses the gl O is Open is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralGLSetIsOpenAndIsCompact.lean#L7-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralGLSetIsOpenAndIsCompact.lean#L7-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralGLSetIsOpenAndIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.GLift

theorem GlobalTheory.JR.GLift.glO_isOpen_isCompact : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [ProperSpace F] (n : ℕ), IsOpen (glO n F) ∧ IsCompact (glO n F) := by sorry
