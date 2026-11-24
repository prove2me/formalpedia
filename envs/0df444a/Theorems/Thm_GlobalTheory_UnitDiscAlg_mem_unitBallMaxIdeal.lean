-- Prove2me | Theorems.Thm_GlobalTheory_UnitDiscAlg_mem_unitBallMaxIdeal
-- name    : GlobalTheory.UnitDiscAlg.mem_unitBallMaxIdeal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:37:35.837745+00:00
-- url     : https://prove2.me/theorems/48e5bac7-ef9d-45c9-984d-189d1f5afe14
-- title:
--   Unit Disc Alg: mem unit Ball Max Ideal
-- statement:
--   The Unit Disc Alg construction uses the mem unit Ball Max Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixTopnil.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixTopnil.lean#L14-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormDetOneAddSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ClosedBallValuationSubringToSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.UnitDiscAlg
variable (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]

theorem GlobalTheory.UnitDiscAlg.mem_unitBallMaxIdeal {t : unitBallSubring E} :
    t ∈ unitBallMaxIdeal E ↔ ‖(t : E)‖ < 1 := by sorry
