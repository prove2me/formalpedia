-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_span_pow_anti
-- name    : GroundTheory.PAdicHodge.TeichLift.span_pow_anti
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:30.292375+00:00
-- url     : https://prove2.me/theorems/28ab7b96-849d-4a9b-a6db-467986bbe803
-- title:
--   Teich Lift: span pow anti
-- statement:
--   The Teich Lift construction uses the span pow anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaTeich.lean#L65-L68

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

theorem GroundTheory.PAdicHodge.TeichLift.span_pow_anti {m n : ℕ} (h : n ≤ m) : Ideal.span {T.π ^ m} ≤ Ideal.span {T.π ^ n} := by sorry
