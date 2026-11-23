-- Prove2me | Theorems.Thm_GlobalTheory_JR_SLGen_wS_inv_coe
-- name    : GlobalTheory.JR.SLGen.wS_inv_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:10.57099+00:00
-- url     : https://prove2.me/theorems/795c6e83-b0b1-4099-b9f7-b640eb8d3418
-- title:
--   SLGen: w S inv coe
-- statement:
--   The SLGen construction uses the w S inv coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2GeneratedWeylUnipotent.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2GeneratedWeylUnipotent.lean#L28-L30

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

theorem GlobalTheory.JR.SLGen.wS_inv_coe :
    (((wS F)⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := by sorry
