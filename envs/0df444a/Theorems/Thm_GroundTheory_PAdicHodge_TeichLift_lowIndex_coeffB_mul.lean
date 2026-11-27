-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_lowIndex_coeffB_mul
-- name    : GroundTheory.PAdicHodge.TeichLift.lowIndex_coeffB_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:01:32.554416+00:00
-- url     : https://prove2.me/theorems/0abb1d7b-7a64-5fc0-86a1-a012e1fcd888
-- title:
--   Teich Lift: low Index coeff B mul
-- statement:
--   The Teich Lift construction uses the low Index coeff B mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L646-L667
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L646-L667

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

theorem GroundTheory.PAdicHodge.TeichLift.lowIndex_coeffB_mul (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hb : ConvergesAt (T.coeffB b) ρ)
    (hc : ConvergesAt (T.coeffB c) ρ) (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    lowIndex (T.coeffB (b * c)) ρ = lowIndex (T.coeffB b) ρ + lowIndex (T.coeffB c) ρ := by sorry
