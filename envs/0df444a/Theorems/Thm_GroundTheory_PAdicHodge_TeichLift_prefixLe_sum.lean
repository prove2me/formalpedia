-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_sum
-- name    : GroundTheory.PAdicHodge.TeichLift.prefixLe_sum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:45:38.677994+00:00
-- url     : https://prove2.me/theorems/d492a1e5-17b1-45b5-a158-50b3803a4b8a
-- title:
--   Teich Lift: prefix Le sum
-- statement:
--   The Teich Lift construction uses the prefix Le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L463-L471
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L463-L471

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

theorem GroundTheory.PAdicHodge.TeichLift.prefixLe_sum {ι : Type*} (s : Finset ι) (f : ι → Γ) {n : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i ∈ s, T.PrefixLe (f i) n b) : T.PrefixLe (∑ i ∈ s, f i) n b := by sorry
