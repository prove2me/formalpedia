-- Prove2me | Theorems.Thm_GlobalTheory_cubeComplex_X
-- name    : GlobalTheory.cubeComplex_X
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:43:48.21529+00:00
-- url     : https://prove2.me/theorems/222e3260-66a8-51dc-8461-4d2f92638782
-- title:
--   Global Theory: cube Complex X
-- statement:
--   The Global Theory construction uses the cube Complex X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L375-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L375-L376

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
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]

theorem GlobalTheory.cubeComplex_X (A : Cube.{v} ι R) (p : ℕ) :
    (cubeComplex A).X p = ModuleCat.of R (Cube.Term A p) := by sorry
