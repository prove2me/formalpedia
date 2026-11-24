-- Prove2me | Theorems.Thm_GlobalTheory_IdemLift_step_sub
-- name    : GlobalTheory.IdemLift.step_sub
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:03.19407+00:00
-- url     : https://prove2.me/theorems/04cccf15-cfda-4e64-9f3d-98325195508a
-- title:
--   Idem Lift: step sub
-- statement:
--   The Idem Lift construction uses the step sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralIdempotentLiftNewton.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralIdempotentLiftNewton.lean#L23-L25

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

theorem GlobalTheory.IdemLift.step_sub (y : Matrix (Fin n) (Fin n) E) :
    step y - y = (y * y - y) * (1 - (y + y)) := by sorry
