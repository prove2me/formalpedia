-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_compact_open_units_subgroup_continuous_sqrt
-- name    : GlobalTheory.T.exists_compact_open_units_subgroup_continuous_sqrt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:33:53.328379+00:00
-- url     : https://prove2.me/theorems/698470eb-197d-493e-b8d0-3a47809d309f
-- title:
--   T: exists compact open units subgroup continuous sqrt
-- statement:
--   The T construction uses the exists compact open units subgroup continuous sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsCompactOpenUnitsSubgroupContinuousSqrtStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsCompactOpenUnitsSubgroupContinuousSqrtStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsCompactOpenUnitsSubgroupContinuousSqrt
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsCompactOpenUnitsSubgroupContinuousSqrtStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_compact_open_units_subgroup_continuous_sqrt : ∀ (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K], (2 : K) ≠ 0 → ∃ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s := by sorry
