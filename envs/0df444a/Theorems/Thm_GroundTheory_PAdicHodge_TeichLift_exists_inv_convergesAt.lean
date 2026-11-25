-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_exists_inv_convergesAt
-- name    : GroundTheory.PAdicHodge.TeichLift.exists_inv_convergesAt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:27:20.037701+00:00
-- url     : https://prove2.me/theorems/ed0bf901-e7f0-420a-b0bb-65097652410a
-- title:
--   Teich Lift: exists inv converges At
-- statement:
--   The Teich Lift construction uses the exists inv converges At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L756-L848
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L756-L848

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

theorem GroundTheory.PAdicHodge.TeichLift.exists_inv_convergesAt {u : Γ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hu : ConvergesAt (T.zcoeff u) ρ) (h1 : T.coeff u 0 = 1) :
    ∃ v : Γ, u * v = 1 ∧ ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' < 1 ∧ ConvergesAt (T.zcoeff v) ρ' := by sorry
