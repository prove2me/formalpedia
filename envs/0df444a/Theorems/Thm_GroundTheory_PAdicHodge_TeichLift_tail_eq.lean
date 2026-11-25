-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_tail_eq
-- name    : GroundTheory.PAdicHodge.TeichLift.tail_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:57.152211+00:00
-- url     : https://prove2.me/theorems/e9cd86ab-6c46-478e-8e6b-43ff83870bab
-- title:
--   Teich Lift: tail eq
-- statement:
--   The Teich Lift construction uses the tail eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L132-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L132-L135

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

theorem GroundTheory.PAdicHodge.TeichLift.tail_eq {x y : Γ} {a : L} (h : x = T.teich a + T.π * y) : T.tail x = y := by sorry
