-- Prove2me | Theorems.Thm_GlobalTheory_IdemLift_step_sq
-- name    : GlobalTheory.IdemLift.step_sq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:12:53.51889+00:00
-- url     : https://prove2.me/theorems/ccb6faad-89a4-4611-9b0c-30af4d65edbb
-- title:
--   Idem Lift: step sq
-- statement:
--   The Idem Lift construction uses the step sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralIdempotentLiftNewton.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralIdempotentLiftNewton.lean#L18-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralIdempotentLiftNewton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory GlobalTheory.IdemLift
open Filter Topology
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

theorem GlobalTheory.IdemLift.step_sq (y : Matrix (Fin n) (Fin n) E) :
    step y * step y - step y = (y * y - y) * (y * y - y) *
      ((y * y - y) + (y * y - y) + (y * y - y) + (y * y - y) - (1 + 1 + 1)) := by sorry
