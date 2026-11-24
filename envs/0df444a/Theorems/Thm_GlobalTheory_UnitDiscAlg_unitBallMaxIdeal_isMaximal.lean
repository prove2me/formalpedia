-- Prove2me | Theorems.Thm_GlobalTheory_UnitDiscAlg_unitBallMaxIdeal_isMaximal
-- name    : GlobalTheory.UnitDiscAlg.unitBallMaxIdeal_isMaximal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:26:49.042537+00:00
-- url     : https://prove2.me/theorems/1d1986c8-79c6-4f1e-b0f2-ac6a0f3df907
-- title:
--   Unit Disc Alg: unit Ball Max Ideal is Maximal
-- statement:
--   The Unit Disc Alg construction uses the unit Ball Max Ideal is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixTopnil.lean#L17-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixTopnil.lean#L17-L35

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

theorem GlobalTheory.UnitDiscAlg.unitBallMaxIdeal_isMaximal : (unitBallMaxIdeal E).IsMaximal := by sorry
