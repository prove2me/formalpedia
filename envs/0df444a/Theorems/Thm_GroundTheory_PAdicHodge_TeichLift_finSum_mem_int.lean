-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_finSum_mem_int
-- name    : GroundTheory.PAdicHodge.TeichLift.finSum_mem_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:39.517467+00:00
-- url     : https://prove2.me/theorems/6b62c6ff-6e36-4aea-be68-06f8739d35d3
-- title:
--   Teich Lift: fin Sum mem int
-- statement:
--   The Teich Lift construction uses the fin Sum mem int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L356-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L356-L358

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

theorem GroundTheory.PAdicHodge.TeichLift.finSum_mem_int {a : ℕ → L} {n : ℕ} (h : ∀ i < n, ‖a i‖ ≤ 1) : T.finSum a n ∈ T.int := by sorry
