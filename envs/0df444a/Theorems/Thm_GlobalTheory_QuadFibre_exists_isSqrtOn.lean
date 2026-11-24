-- Prove2me | Theorems.Thm_GlobalTheory_QuadFibre_exists_isSqrtOn
-- name    : GlobalTheory.QuadFibre.exists_isSqrtOn
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:09:54.180802+00:00
-- url     : https://prove2.me/theorems/c824e504-d4ae-40a5-92e9-4daeea8a920a
-- title:
--   Quad Fibre: exists is Sqrt On
-- statement:
--   The Quad Fibre construction uses the exists is Sqrt On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsCompactOpenUnitsSubgroupContinuousSqrt.lean#L20-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsCompactOpenUnitsSubgroupContinuousSqrt.lean#L20-L64

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

theorem GlobalTheory.QuadFibre.exists_isSqrtOn (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ProperSpace K] (h2 : (2 : K) ≠ 0) : ∃ (U : Set K) (s : K → K), IsSqrtOn U s := by sorry
