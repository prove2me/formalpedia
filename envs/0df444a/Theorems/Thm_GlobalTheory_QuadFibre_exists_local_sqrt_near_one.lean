-- Prove2me | Theorems.Thm_GlobalTheory_QuadFibre_exists_local_sqrt_near_one
-- name    : GlobalTheory.QuadFibre.exists_local_sqrt_near_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:10:53.952274+00:00
-- url     : https://prove2.me/theorems/84ecc317-441b-4b4e-903b-da3457bcf8d8
-- title:
--   Quad Fibre: exists local sqrt near one
-- statement:
--   The Quad Fibre construction uses the exists local sqrt near one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsCompactOpenUnitsSubgroupContinuousSqrt.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsCompactOpenUnitsSubgroupContinuousSqrt.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsCompactOpenUnitsSubgroupContinuousSqrt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open GlobalTheory GlobalTheory.QuadFibre

theorem GlobalTheory.QuadFibre.exists_local_sqrt_near_one (K : Type) [NontriviallyNormedField K] [CompleteSpace K]
    (h2 : (2 : K) ≠ 0) : ∃ (N : Set K) (g : K → K), IsOpen N ∧ (1 : K) ∈ N ∧ ContinuousOn g N ∧
      ∀ u ∈ N, g u ^ 2 = u := by sorry
