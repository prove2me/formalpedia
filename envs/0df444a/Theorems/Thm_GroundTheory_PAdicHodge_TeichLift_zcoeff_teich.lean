-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_zcoeff_teich
-- name    : GroundTheory.PAdicHodge.TeichLift.zcoeff_teich
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:34:27.983831+00:00
-- url     : https://prove2.me/theorems/a44c3874-61de-5237-bd61-fcb0a646db49
-- title:
--   Teich Lift: zcoeff teich
-- statement:
--   The Teich Lift construction uses the zcoeff teich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L567-L568
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L567-L568

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
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
open GroundTheory GroundTheory.PAdicHodge
open Laurent Filter Topology
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ) {ρ : ℝ}

theorem GroundTheory.PAdicHodge.TeichLift.zcoeff_teich (c : L) : T.zcoeff (T.teich c) = Pi.single 0 c := by sorry
