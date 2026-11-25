-- Prove2me | Theorems.Thm_GlobalTheory_Cube_d_termDirectSum
-- name    : GlobalTheory.Cube.d_termDirectSum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:52.232809+00:00
-- url     : https://prove2.me/theorems/da5f5e0d-7958-49b6-9f69-2a2b1763718e
-- title:
--   Cube: d term Direct Sum
-- statement:
--   The Cube construction uses the d term Direct Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L1074-L1081
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L1074-L1081

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
open DirectSum
variable {R : Type u} [Ring R] {κ : Type} [DecidableEq κ]
variable {ι : Type}
variable [LinearOrder ι]

theorem GlobalTheory.Cube.d_termDirectSum (A : κ → Cube.{v} ι R) (p : ℕ) (x : ⨁ k, Cube.Term (A k) p) :
    Cube.d (Cube.directSum A) p (Cube.termDirectSum A p x) =
      Cube.termDirectSum A (p + 1) (DirectSum.lmap (fun k => Cube.d (A k) p) x) := by sorry
