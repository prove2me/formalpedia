-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_isTest_mOp
-- name    : GlobalTheory.JR.WeilQuad.isTest_mOp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:38:54.103987+00:00
-- url     : https://prove2.me/theorems/04337f6b-8d97-4fd7-b671-3b461ea54d82
-- title:
--   Weil Quad: is Test m Op
-- statement:
--   The Weil Quad construction uses the is Test m Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilUnipotentTorusPreserveTest.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilUnipotentTorusPreserveTest.lean#L44-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilUnipotentTorusPreserveTest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem GlobalTheory.JR.WeilQuad.isTest_mOp (A : Et F E) (ω : A.K → ℂ) (s : A.Kˣ) {φ : A.L → ℂ} (hφ : IsTest φ) :
    IsTest (mOp A ω s φ) := by sorry
