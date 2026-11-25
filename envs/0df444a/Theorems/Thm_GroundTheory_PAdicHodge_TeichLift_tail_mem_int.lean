-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_tail_mem_int
-- name    : GroundTheory.PAdicHodge.TeichLift.tail_mem_int
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:52.679578+00:00
-- url     : https://prove2.me/theorems/b1e112ae-77c0-4438-b614-b3613a16902e
-- title:
--   Teich Lift: tail mem int
-- statement:
--   The Teich Lift construction uses the tail mem int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L349-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L349-L354

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

theorem GroundTheory.PAdicHodge.TeichLift.tail_mem_int {x : Γ} (hx : x ∈ T.int) : T.tail x ∈ T.int := by sorry
