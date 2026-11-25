-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_teich_mul
-- name    : GroundTheory.PAdicHodge.TeichLift.coeff_teich_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:46.998959+00:00
-- url     : https://prove2.me/theorems/1abab3a1-ed52-4732-a42f-f858ff6bb4d3
-- title:
--   Teich Lift: coeff teich mul
-- statement:
--   The Teich Lift construction uses the coeff teich mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L298-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L298-L304

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

theorem GroundTheory.PAdicHodge.TeichLift.coeff_teich_mul (c : L) (x : Γ) (n : ℕ) : T.coeff (T.teich c * x) n = c * T.coeff x n := by sorry
