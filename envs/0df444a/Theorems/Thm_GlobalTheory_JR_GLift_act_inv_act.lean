-- Prove2me | Theorems.Thm_GlobalTheory_JR_GLift_act_inv_act
-- name    : GlobalTheory.JR.GLift.act_inv_act
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:31:43.367801+00:00
-- url     : https://prove2.me/theorems/617ddae0-00c0-4187-bf21-472c0bd425ff
-- title:
--   GLift: act inv act
-- statement:
--   The GLift construction uses the act inv act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorGLBlockGlBorderedConjugationActionI.lean#L38-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorGLBlockGlBorderedConjugationActionI.lean#L38-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorGLBlockGlBorderedConjugationActionI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.GLift

theorem GlobalTheory.JR.GLift.act_inv_act {F : Type} [Field F] {n : ℕ} (k : GL (Fin n) F) (Y : Gl n F) :
    act k⁻¹ (act k Y) = Y := by sorry
