-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_finSum_mem_span_of_eq_zero
-- name    : GroundTheory.PAdicHodge.TeichLift.finSum_mem_span_of_eq_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:01:02.290151+00:00
-- url     : https://prove2.me/theorems/93f94c3b-e984-53e3-b018-5afc1440fa95
-- title:
--   Teich Lift: fin Sum mem span of eq zero
-- statement:
--   The Teich Lift construction uses the fin Sum mem span of eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L172-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L172-L176

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

theorem GroundTheory.PAdicHodge.TeichLift.finSum_mem_span_of_eq_zero {a : ℕ → L} {n m : ℕ} (h : ∀ i < m, a i = 0) (hmn : m ≤ n) :
    T.finSum a n ∈ Ideal.span {T.π ^ m} := by sorry
