-- Prove2me | Theorems.Thm_GlobalTheory_NTr_exists_diff_one
-- name    : GlobalTheory.NTr.exists_diff_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:30:28.652893+00:00
-- url     : https://prove2.me/theorems/fa611345-8f85-4169-a77e-8abf0766ca3d
-- title:
--   NTr: exists diff one
-- statement:
--   The NTr construction uses the exists diff one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticIntegralTraceFormPerfect.lean#L192-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticIntegralTraceFormPerfect.lean#L192-L230

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.NTr
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]

theorem GlobalTheory.NTr.exists_diff_one (h2 : ‖(2 : F)‖ < 1) : ∃ w : E, ‖w‖ ≤ 1 ∧ ‖w - star w‖ = 1 := by sorry
