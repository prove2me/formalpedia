-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_algebraMap_teich_mem_Econ
-- name    : GroundTheory.PAdicHodge.TeichLift.algebraMap_teich_mem_Econ
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:06:23.935229+00:00
-- url     : https://prove2.me/theorems/069977a2-d44b-5c77-bc38-0d781cf74bd3
-- title:
--   Teich Lift: algebra Map teich mem Econ
-- statement:
--   The Teich Lift construction uses the algebra Map teich mem Econ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L688-L690
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L688-L690

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
variable {b c : T.B}

theorem GroundTheory.PAdicHodge.TeichLift.algebraMap_teich_mem_Econ (c : L) (ρ : Set.Ioo (0 : ℝ) 1) :
    algebraMap Γ T.B (T.teich c) ∈ T.Econ ρ := by sorry
