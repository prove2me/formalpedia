-- Prove2me | Theorems.Thm_GlobalTheory_cubeComplex_const_exactAt
-- name    : GlobalTheory.cubeComplex_const_exactAt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:14:44.817552+00:00
-- url     : https://prove2.me/theorems/c9d22b4e-9e5c-43ea-8eba-78c65e29cfe4
-- title:
--   Global Theory: cube Complex const exact At
-- statement:
--   The Global Theory construction uses the cube Complex const exact At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L620-L623
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L620-L623

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

theorem GlobalTheory.cubeComplex_const_exactAt [Nonempty ι] (M : ModuleCat.{v} R) (p : ℕ) :
    (cubeComplex (Cube.const ι M)).ExactAt p := by sorry
