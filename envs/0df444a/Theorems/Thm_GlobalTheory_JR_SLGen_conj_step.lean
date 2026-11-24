-- Prove2me | Theorems.Thm_GlobalTheory_JR_SLGen_conj_step
-- name    : GlobalTheory.JR.SLGen.conj_step
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:36:56.889356+00:00
-- url     : https://prove2.me/theorems/f3bf12e4-4e89-47cc-90c3-a52da424e112
-- title:
--   SLGen: conj step
-- statement:
--   The SLGen construction uses the conj step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2GeneratedWeylUnipotent.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2GeneratedWeylUnipotent.lean#L39-L45

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2GeneratedWeylUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SLGen
variable {F : Type} [Field F]

theorem GlobalTheory.JR.SLGen.conj_step {ϖ : F} (hϖ : ϖ ≠ 0) (t : F) :
    (nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹)⁻¹ * nS t *
      (nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹) = nS (ϖ⁻¹ ^ 2 * t) := by sorry
