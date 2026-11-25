-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_lowIndex_zcoeff_mul
-- name    : GroundTheory.PAdicHodge.TeichLift.lowIndex_zcoeff_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:28:38.188642+00:00
-- url     : https://prove2.me/theorems/64fcf79d-a67d-4000-a4f3-13c248998d8f
-- title:
--   Teich Lift: low Index zcoeff mul
-- statement:
--   The Teich Lift construction uses the low Index zcoeff mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L429-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L429-L433

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
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
open GroundTheory GroundTheory.PAdicHodge
open Laurent Filter Topology
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
variable {ρ : ℝ}

theorem GroundTheory.PAdicHodge.TeichLift.lowIndex_zcoeff_mul {x y : Γ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hx : ConvergesAt (T.zcoeff x) ρ) (hy : ConvergesAt (T.zcoeff y) ρ) (hx0 : x ≠ 0)
    (hy0 : y ≠ 0) :
    lowIndex (T.zcoeff (x * y)) ρ = lowIndex (T.zcoeff x) ρ + lowIndex (T.zcoeff y) ρ := by sorry
