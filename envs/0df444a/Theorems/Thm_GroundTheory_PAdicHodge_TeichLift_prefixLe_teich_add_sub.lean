-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_teich_add_sub
-- name    : GroundTheory.PAdicHodge.TeichLift.prefixLe_teich_add_sub
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:45:57.86556+00:00
-- url     : https://prove2.me/theorems/1b1fa3ed-01fe-4c4d-ac0a-a3884657596a
-- title:
--   Teich Lift: prefix Le teich add sub
-- statement:
--   The Teich Lift construction uses the prefix Le teich add sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L606-L635
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L606-L635

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

theorem GroundTheory.PAdicHodge.TeichLift.prefixLe_teich_add_sub {a e : L} (h : ‖e‖ ≤ ‖a‖) (k : ℕ) :
    T.PrefixLe (T.teich (a + e) - T.teich a - T.teich e) k
      (‖a‖ ^ (1 - ((p ^ k : ℕ) : ℝ)⁻¹) * ‖e‖ ^ ((p ^ k : ℕ) : ℝ)⁻¹) := by sorry
