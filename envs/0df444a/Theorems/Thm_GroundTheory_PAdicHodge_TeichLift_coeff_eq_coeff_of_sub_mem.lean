-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_eq_coeff_of_sub_mem
-- name    : GroundTheory.PAdicHodge.TeichLift.coeff_eq_coeff_of_sub_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:56.78716+00:00
-- url     : https://prove2.me/theorems/61cbb96c-d3f4-4d86-a551-7f0f3a5d7905
-- title:
--   Teich Lift: coeff eq coeff of sub mem
-- statement:
--   The Teich Lift construction uses the coeff eq coeff of sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L261-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L261-L265

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

theorem GroundTheory.PAdicHodge.TeichLift.coeff_eq_coeff_of_sub_mem {x y : Γ} {n : ℕ} (h : x - y ∈ Ideal.span {T.π ^ (n + 1)}) :
    ∀ m ≤ n, T.coeff x m = T.coeff y m := by sorry
