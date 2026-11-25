-- Prove2me | Theorems.Thm_GlobalTheory_Cube_termBaseChangeEquiv_apply
-- name    : GlobalTheory.Cube.termBaseChangeEquiv_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:06.283196+00:00
-- url     : https://prove2.me/theorems/b5b4c6ec-2074-445e-b95d-9a3bf358ca79
-- title:
--   Cube: term Base Change Equiv apply
-- statement:
--   The Cube construction uses the term Base Change Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L886-L888
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L886-L888

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

theorem GlobalTheory.Cube.termBaseChangeEquiv_apply [Finite ι] (A : Cube.{v} ι R) (p : ℕ)
    (x : S ⊗[R] Cube.Term A p) :
    Cube.termBaseChangeEquiv S A p x = Cube.termBaseChange S A p x := by sorry
