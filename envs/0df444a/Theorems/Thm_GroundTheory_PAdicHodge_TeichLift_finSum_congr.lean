-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_finSum_congr
-- name    : GroundTheory.PAdicHodge.TeichLift.finSum_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:32.473814+00:00
-- url     : https://prove2.me/theorems/86019516-bb6f-4402-8ca6-f0ca15807db7
-- title:
--   Teich Lift: fin Sum congr
-- statement:
--   The Teich Lift construction uses the fin Sum congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L168-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L168-L170

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

theorem GroundTheory.PAdicHodge.TeichLift.finSum_congr {a b : ℕ → L} {n : ℕ} (h : ∀ i < n, a i = b i) :
    T.finSum a n = T.finSum b n := by sorry
