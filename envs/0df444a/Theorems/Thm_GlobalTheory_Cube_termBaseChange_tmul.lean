-- Prove2me | Theorems.Thm_GlobalTheory_Cube_termBaseChange_tmul
-- name    : GlobalTheory.Cube.termBaseChange_tmul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:18.834298+00:00
-- url     : https://prove2.me/theorems/99c96bd2-f063-4298-a83b-3aa3f553eb1c
-- title:
--   Cube: term Base Change tmul
-- statement:
--   The Cube construction uses the term Base Change tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L872-L874
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L872-L874

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

theorem GlobalTheory.Cube.termBaseChange_tmul (A : Cube.{v} ι R) (p : ℕ) (c : S) (x : Cube.Term A p)
    (s : {s : Finset ι // s.card = p}) :
    Cube.termBaseChange S A p (c ⊗ₜ[R] x) s = c ⊗ₜ[R] x s := by sorry
