-- Prove2me | Theorems.Thm_GlobalTheory_Cube_flat_term
-- name    : GlobalTheory.Cube.flat_term
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:08.573858+00:00
-- url     : https://prove2.me/theorems/c2ed2693-d698-495e-adc7-2c150aee4b4c
-- title:
--   Cube: flat term
-- statement:
--   The Cube construction uses the flat term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L917-L924
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L917-L924

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

theorem GlobalTheory.Cube.flat_term [Finite ι] (A : Cube.{v} ι R) (p : ℕ)
    (h : ∀ s : Finset ι, s.card = p → Module.Flat R (A.obj s)) :
    Module.Flat R (Cube.Term A p) := by sorry
