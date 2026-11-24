-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_teich_sub_pow_mem
-- name    : GroundTheory.PAdicHodge.TeichLift.teich_sub_pow_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:05.019373+00:00
-- url     : https://prove2.me/theorems/11e3b744-49b7-4f14-a3d1-aee5d69133ed
-- title:
--   Teich Lift: teich sub pow mem
-- statement:
--   The Teich Lift construction uses the teich sub pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L110-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L110-L119

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

theorem GroundTheory.PAdicHodge.TeichLift.teich_sub_pow_mem (a : L) (n : ℕ) (z : Γ)
    (hz : T.red z = (((frobeniusEquiv L p).symm : L →+* L))^[n] a) :
    T.teich a - z ^ p ^ n ∈ Ideal.span {T.π ^ (n + 1)} := by sorry
