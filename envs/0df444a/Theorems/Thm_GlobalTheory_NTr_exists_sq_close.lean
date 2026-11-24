-- Prove2me | Theorems.Thm_GlobalTheory_NTr_exists_sq_close
-- name    : GlobalTheory.NTr.exists_sq_close
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:30:20.911153+00:00
-- url     : https://prove2.me/theorems/b8f26cc3-e9d5-4497-848b-948f497a2cf1
-- title:
--   NTr: exists sq close
-- statement:
--   The NTr construction uses the exists sq close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticIntegralTraceFormPerfect.lean#L73-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticIntegralTraceFormPerfect.lean#L73-L133

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
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem GlobalTheory.NTr.exists_sq_close [ProperSpace K] (h2 : ‖(2 : K)‖ < 1) (n : K) (hn : ‖n‖ ≤ 1) :
    ∃ s : K, ‖s‖ ≤ 1 ∧ ‖n - s ^ 2‖ < 1 := by sorry
