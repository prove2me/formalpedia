-- Prove2me | Theorems.Thm_GlobalTheory_JR_GLift_coe_glOSub
-- name    : GlobalTheory.JR.GLift.coe_glOSub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:11:37.087618+00:00
-- url     : https://prove2.me/theorems/cc038606-b0ba-44f4-a890-eec387d3b59a
-- title:
--   GLift: coe gl OSub
-- statement:
--   The GLift construction uses the coe gl OSub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormMulApplyLeOne.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormMulApplyLeOne.lean#L41-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.GLift

theorem GlobalTheory.JR.GLift.coe_glOSub (n : ℕ) (F : Type) [NormedField F] [IsUltrametricDist F] :
    (glOSub n F : Set (GL (Fin n) F)) = glO n F := by sorry
