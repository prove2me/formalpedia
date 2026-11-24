-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_rpow_mix_le
-- name    : GroundTheory.PAdicHodge.TeichLift.rpow_mix_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:45.774806+00:00
-- url     : https://prove2.me/theorems/7e7bb67c-39f9-4216-ab5e-e27b5044bb12
-- title:
--   Teich Lift: rpow mix le
-- statement:
--   The Teich Lift construction uses the rpow mix le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L595-L600
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L595-L600

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

theorem GroundTheory.PAdicHodge.TeichLift.rpow_mix_le {δ B t : ℝ} (hδ : 0 ≤ δ) (hδB : δ ≤ B) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    B ^ (1 - t) * δ ^ t ≤ B := by sorry
