-- Prove2me | Theorems.Thm_GlobalTheory_Cube_finite_term
-- name    : GlobalTheory.Cube.finite_term
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:51.673725+00:00
-- url     : https://prove2.me/theorems/2639cd17-af64-46ff-b3f1-3431580abf95
-- title:
--   Cube: finite term
-- statement:
--   The Cube construction uses the finite term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L911-L915
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L911-L915

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
open TensorProduct
variable {ι : Type} {R : Type u} [CommRing R]
variable (S : Type u') [CommRing S] [Algebra R S]

theorem GlobalTheory.Cube.finite_term {R : Type u} [Ring R] [Finite ι] (A : Cube.{v} ι R) (p : ℕ)
    (h : ∀ s : Finset ι, s.card = p → Module.Finite R (A.obj s)) :
    Module.Finite R (Cube.Term A p) := by sorry
