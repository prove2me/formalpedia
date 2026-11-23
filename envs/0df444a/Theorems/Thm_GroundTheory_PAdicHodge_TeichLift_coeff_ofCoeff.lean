-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
-- name    : GroundTheory.PAdicHodge.TeichLift.coeff_ofCoeff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:49.589597+00:00
-- url     : https://prove2.me/theorems/f168b44b-e6d9-4310-9f64-e8ec399bb475
-- title:
--   Teich Lift: coeff of Coeff
-- statement:
--   The Teich Lift construction uses the coeff of Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L256-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L256-L257

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

theorem GroundTheory.PAdicHodge.TeichLift.coeff_ofCoeff (a : ℕ → L) : T.coeff (T.ofCoeff a) = a := by sorry
