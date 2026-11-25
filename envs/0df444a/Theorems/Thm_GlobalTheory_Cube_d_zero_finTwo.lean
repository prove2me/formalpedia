-- Prove2me | Theorems.Thm_GlobalTheory_Cube_d_zero_finTwo
-- name    : GlobalTheory.Cube.d_zero_finTwo
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:49.187224+00:00
-- url     : https://prove2.me/theorems/95a9fc8e-2a7e-43ad-8816-65bd3999247d
-- title:
--   Cube: d zero fin Two
-- statement:
--   The Cube construction uses the d zero fin Two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L1184-L1189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L1184-L1189

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
variable {R : Type u} [Ring R]

theorem GlobalTheory.Cube.d_zero_finTwo (A : Cube.{v} (Fin 2) R) (x : Cube.Term A 0) :
    Cube.termOneFinTwo A (Cube.d A 0 x) =
      (Cube.res A (Finset.empty_subset _) (Cube.termZeroEquiv A x),
        Cube.res A (Finset.empty_subset _) (Cube.termZeroEquiv A x)) := by sorry
