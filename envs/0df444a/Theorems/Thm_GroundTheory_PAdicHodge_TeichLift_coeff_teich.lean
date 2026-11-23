-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_teich
-- name    : GroundTheory.PAdicHodge.TeichLift.coeff_teich
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:29.686401+00:00
-- url     : https://prove2.me/theorems/96b0b20e-508d-47f2-a29b-2a5583860bc9
-- title:
--   Teich Lift: coeff teich
-- statement:
--   The Teich Lift construction uses the coeff teich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L306-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L306-L317

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

theorem GroundTheory.PAdicHodge.TeichLift.coeff_teich (c : L) (n : ℕ) : T.coeff (T.teich c) n = if n = 0 then c else 0 := by sorry
