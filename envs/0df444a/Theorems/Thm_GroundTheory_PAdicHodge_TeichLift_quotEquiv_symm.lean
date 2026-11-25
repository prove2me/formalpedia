-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_quotEquiv_symm
-- name    : GroundTheory.PAdicHodge.TeichLift.quotEquiv_symm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:55.120471+00:00
-- url     : https://prove2.me/theorems/8b34d2d6-5af4-475c-bc0c-8ef2ed08cd55
-- title:
--   Teich Lift: quot Equiv symm
-- statement:
--   The Teich Lift construction uses the quot Equiv symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L78-L80

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

theorem GroundTheory.PAdicHodge.TeichLift.quotEquiv_symm (a : L) (x : Γ) (h : T.red x = a) :
    T.quotEquiv.symm a = Ideal.Quotient.mk T.I x := by sorry
