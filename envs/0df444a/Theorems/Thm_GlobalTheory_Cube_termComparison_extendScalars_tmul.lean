-- Prove2me | Theorems.Thm_GlobalTheory_Cube_termComparison_extendScalars_tmul
-- name    : GlobalTheory.Cube.termComparison_extendScalars_tmul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:06.214089+00:00
-- url     : https://prove2.me/theorems/064c584c-5874-5a9d-b058-c4cdeee499c8
-- title:
--   Cube: term Comparison extend Scalars tmul
-- statement:
--   The Cube construction uses the term Comparison extend Scalars tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L845-L848
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L845-L848

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
open ChangeOfRings

theorem GlobalTheory.Cube.termComparison_extendScalars_tmul {S : Type u'} [CommRing S] (f : R →+* S)
    (A : Cube.{v} ι R) (p : ℕ) (c : S) (x : Cube.Term A p) (s : {s : Finset ι // s.card = p}) :
    (Cube.termComparison (ModuleCat.extendScalars f) A p).hom (c ⊗ₜ[R,f] x) s =
      c ⊗ₜ[R,f] x s := by sorry
