-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_norm_coeff_add_sub_le
-- name    : GroundTheory.PAdicHodge.TeichLift.norm_coeff_add_sub_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:01:21.599358+00:00
-- url     : https://prove2.me/theorems/aebef33f-a79c-41a6-b0a2-2a610ef02806
-- title:
--   Teich Lift: norm coeff add sub le
-- statement:
--   The Teich Lift construction uses the norm coeff add sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L666-L725
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L666-L725

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

theorem GroundTheory.PAdicHodge.TeichLift.norm_coeff_add_sub_le (n : ℕ) : ∀ {x y : Γ} {B δ : ℝ}, 0 ≤ δ → δ ≤ B →
    T.PrefixLe x n B → T.PrefixLe y n δ → ∀ m ≤ n,
      ‖T.coeff (x + y) m - T.coeff x m‖ ≤ B ^ (1 - coeffHolderExp p n) * δ ^ coeffHolderExp p n := by sorry
