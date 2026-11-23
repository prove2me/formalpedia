-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_sub_partialSum_mem
-- name    : GroundTheory.PAdicHodge.TeichLift.sub_partialSum_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:02.114187+00:00
-- url     : https://prove2.me/theorems/7dac0283-e2f9-44a2-812d-52abc7f645c7
-- title:
--   Teich Lift: sub partial Sum mem
-- statement:
--   The Teich Lift construction uses the sub partial Sum mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L192-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L192-L193

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

theorem GroundTheory.PAdicHodge.TeichLift.sub_partialSum_mem (x : Γ) (n : ℕ) : x - T.partialSum x n ∈ Ideal.span {T.π ^ n} := by sorry
