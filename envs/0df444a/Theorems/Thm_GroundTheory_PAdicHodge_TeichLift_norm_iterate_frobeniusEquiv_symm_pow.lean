-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_norm_iterate_frobeniusEquiv_symm_pow
-- name    : GroundTheory.PAdicHodge.TeichLift.norm_iterate_frobeniusEquiv_symm_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:48.941769+00:00
-- url     : https://prove2.me/theorems/f4a6a980-7e27-4a32-b4ff-73d828c8cf03
-- title:
--   Teich Lift: norm iterate frobenius Equiv symm pow
-- statement:
--   The Teich Lift construction uses the norm iterate frobenius Equiv symm pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L335-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L335-L337

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

theorem GroundTheory.PAdicHodge.TeichLift.norm_iterate_frobeniusEquiv_symm_pow (a : L) (n : ℕ) :
    ‖((((frobeniusEquiv L p).symm : L →+* L))^[n] a)‖ ^ p ^ n = ‖a‖ := by sorry
