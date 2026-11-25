-- Prove2me | Theorems.Thm_GlobalTheory_Cube_d_termBaseChange
-- name    : GlobalTheory.Cube.d_termBaseChange
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:03:05.806334+00:00
-- url     : https://prove2.me/theorems/c4287ba6-ddaa-4890-a475-84ce24afc0f8
-- title:
--   Cube: d term Base Change
-- statement:
--   The Cube construction uses the d term Base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L890-L902
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L890-L902

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

theorem GlobalTheory.Cube.d_termBaseChange [LinearOrder ι] (A : Cube.{v} ι R) (p : ℕ)
    (x : S ⊗[R] Cube.Term A p) :
    Cube.d (Cube.baseChange S A) p (Cube.termBaseChange S A p x) =
      Cube.termBaseChange S A (p + 1) ((Cube.d A p).baseChange S x) := by sorry
