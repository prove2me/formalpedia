-- Prove2me | Theorems.Thm_GlobalTheory_JR_SLGen_exists_unif
-- name    : GlobalTheory.JR.SLGen.exists_unif
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:36:12.230779+00:00
-- url     : https://prove2.me/theorems/a8e4afc8-2875-45e2-b16e-df18b61a03f2
-- title:
--   SLGen: exists unif
-- statement:
--   The SLGen construction uses the exists unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2GeneratedWeylUnipotent.lean#L6-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2GeneratedWeylUnipotent.lean#L6-L20

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

theorem GlobalTheory.JR.SLGen.exists_unif (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] :
    ∃ ϖ : F, ϖ ≠ 0 ∧ ‖ϖ‖ < 1 ∧ ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖ := by sorry
