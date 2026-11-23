-- Prove2me | Theorems.Thm_GlobalTheory_Cube_eq_zero_of_d_eq_zero
-- name    : GlobalTheory.Cube.eq_zero_of_d_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:00.512798+00:00
-- url     : https://prove2.me/theorems/83647451-6919-4976-88e4-66372358ba1a
-- title:
--   Cube: eq zero of d eq zero
-- statement:
--   The Cube construction uses the eq zero of d eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L318-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L318-L334

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
open GlobalTheory.Cube
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]

theorem GlobalTheory.Cube.eq_zero_of_d_eq_zero (A : Cube.{v} ι R) (i : ι) {p : ℕ}
    (hA : ∀ s : Finset ι, i ∉ s → Function.Injective (res A (Finset.subset_insert i s)))
    (x : Term A p) (hx : d A p x = 0) (h0 : ∀ s : {s : Finset ι // s.card = p}, i ∈ s.1 → x s = 0) :
    x = 0 := by sorry
