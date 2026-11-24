-- Prove2me | Theorems.Thm_GlobalTheory_IdemLift_step_comm
-- name    : GlobalTheory.IdemLift.step_comm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:12:46.790792+00:00
-- url     : https://prove2.me/theorems/520491c2-2137-46ca-b338-71d11d88061f
-- title:
--   Idem Lift: step comm
-- statement:
--   The Idem Lift construction uses the step comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralIdempotentLiftNewton.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralIdempotentLiftNewton.lean#L33-L38

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

theorem GlobalTheory.IdemLift.step_comm {y N : Matrix (Fin n) (Fin n) E} (h : y * N = N * y) :
    step y * N = N * step y := by sorry
