-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_teich_mem_int
-- name    : GroundTheory.PAdicHodge.TeichLift.teich_mem_int
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:37.182999+00:00
-- url     : https://prove2.me/theorems/38787a20-657f-4204-a4a5-f53222c58112
-- title:
--   Teich Lift: teich mem int
-- statement:
--   The Teich Lift construction uses the teich mem int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L344-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L344-L347

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

theorem GroundTheory.PAdicHodge.TeichLift.teich_mem_int {a : L} (ha : ‖a‖ ≤ 1) : T.teich a ∈ T.int := by sorry
