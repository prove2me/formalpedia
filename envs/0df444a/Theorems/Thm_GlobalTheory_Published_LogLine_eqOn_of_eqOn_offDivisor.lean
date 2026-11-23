-- Prove2me | Theorems.Thm_GlobalTheory_Published_LogLine_eqOn_of_eqOn_offDivisor
-- name    : GlobalTheory.Published.LogLine.eqOn_of_eqOn_offDivisor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:54.407957+00:00
-- url     : https://prove2.me/theorems/bfbed80e-eb95-449c-99b1-aa32d2e6c6a9
-- title:
--   Log Line: eq On of eq On off Divisor
-- statement:
--   The Log Line construction uses the eq On of eq On off Divisor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ExistsHorizontalGeneratorOfCharts.lean#L70-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ExistsHorizontalGeneratorOfCharts.lean#L70-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__ExistsHorizontalGeneratorOfCharts_f0ad16e2bc421ec8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.LogLine
variable {n : ℕ}

theorem GlobalTheory.Published.LogLine.eqOn_of_eqOn_offDivisor {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (S : Finset (Fin n)) {F G : (Fin n → ℂ) → Y}
    (hF : ContinuousOn F U) (hG : ContinuousOn G U) (h : EqOn F G (offDivisor U S)) :
    EqOn F G U := by sorry
