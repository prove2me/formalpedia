-- Prove2me | Theorems.Thm_GlobalTheory_GradedFixed_orbit_stable
-- name    : GlobalTheory.GradedFixed.orbit_stable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:55.767021+00:00
-- url     : https://prove2.me/theorems/3c0e9280-23a6-4791-840b-db8c763e8873
-- title:
--   Graded Fixed: orbit stable
-- statement:
--   The Graded Fixed construction uses the orbit stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FixedMemOfOrbitHeight.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FixedMemOfOrbitHeight.lean#L28-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FixedMemOfOrbitHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule MulAction
open GlobalTheory GlobalTheory.GradedFixed
variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.GradedFixed.orbit_stable (i : ι) (g : G) {j : ι} (hj : j ∈ orbit G i) : g • j ∈ orbit G i := by sorry
