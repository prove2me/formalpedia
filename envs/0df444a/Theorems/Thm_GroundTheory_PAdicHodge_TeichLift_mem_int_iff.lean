-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_mem_int_iff
-- name    : GroundTheory.PAdicHodge.TeichLift.mem_int_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:01.569692+00:00
-- url     : https://prove2.me/theorems/40040d58-9e56-41c2-9dff-97db7032b19e
-- title:
--   Teich Lift: mem int iff
-- statement:
--   The Teich Lift construction uses the mem int iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L360-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L360-L370

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open Ideal
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CharP L p]
  [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem GroundTheory.PAdicHodge.TeichLift.mem_int_iff {x : Γ} : x ∈ T.int ↔ ∀ n, ‖T.coeff x n‖ ≤ 1 := by sorry
