-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_iff_exists
-- name    : GroundTheory.PAdicHodge.TeichLift.prefixLe_iff_exists
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:06.436529+00:00
-- url     : https://prove2.me/theorems/a0ec99e2-118b-4d7b-8aa8-59816040a4ab
-- title:
--   Teich Lift: prefix Le iff exists
-- statement:
--   The Teich Lift construction uses the prefix Le iff exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L387-L401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L387-L401

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

theorem GroundTheory.PAdicHodge.TeichLift.prefixLe_iff_exists {x : Γ} {n : ℕ} {c : L} (hc : c ≠ 0) :
    T.PrefixLe x n ‖c‖ ↔ ∃ u ∈ T.int, x - T.teich c * u ∈ Ideal.span {T.π ^ (n + 1)} := by sorry
