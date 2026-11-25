-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_mk_sub_finSum_mem
-- name    : GroundTheory.PAdicHodge.TeichLift.mk_sub_finSum_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:45:54.985833+00:00
-- url     : https://prove2.me/theorems/baa307d4-6ae6-4b39-b40f-6f10dbaf5b79
-- title:
--   Teich Lift: mk sub fin Sum mem
-- statement:
--   The Teich Lift construction uses the mk sub fin Sum mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L248-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L248-L254

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

theorem GroundTheory.PAdicHodge.TeichLift.mk_sub_finSum_mem (a : ℕ → L) (n : ℕ) : T.ofCoeff a - T.finSum a n ∈ Ideal.span {T.π ^ n} := by sorry
