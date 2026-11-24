-- Prove2me | Theorems.Thm_GlobalTheory_eventually_eq_zero_of_isBigO_cube_of_doubling
-- name    : GlobalTheory.eventually_eq_zero_of_isBigO_cube_of_doubling
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:19:46.461652+00:00
-- url     : https://prove2.me/theorems/cd6ac86f-7573-472c-bca6-e5bfd3b1493b
-- title:
--   Global Theory: eventually eq zero of is Big O cube of doubling
-- statement:
--   The Global Theory construction uses the eventually eq zero of is Big O cube of doubling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/EventuallyEqZeroOfIsBigOCubeOfDoubling.lean#L85-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/EventuallyEqZeroOfIsBigOCubeOfDoubling.lean#L85-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EventuallyEqZeroOfIsBigOCubeOfDoubling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory

theorem GlobalTheory.eventually_eq_zero_of_isBigO_cube_of_doubling :
    (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : E → ℂ),
      F =O[𝓝 0] (fun z => ‖z‖ ^ 3) →
      (∀ᶠ z in 𝓝 0, F ((2 : ℂ) • z) = 3 * F z + F (-z)) → ∀ᶠ z in 𝓝 0, F z = 0) := by sorry
