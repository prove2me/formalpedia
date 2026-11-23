-- Prove2me | Theorems.Thm_GlobalTheory_Conv_coe_expandConv
-- name    : GlobalTheory.Conv.coe_expandConv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:59:07.929929+00:00
-- url     : https://prove2.me/theorems/62b0a451-e6e3-4c81-b3ce-c297ee839740
-- title:
--   Conv: coe expand Conv
-- statement:
--   The Conv construction uses the coe expand Conv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemPuncturedRingIffPowerSeriesPart.lean#L1014-L1015
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemPuncturedRingIffPowerSeriesPart.lean#L1014-L1015

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries LaurentSeries Topology ENNReal NNReal ContDiff
open Filter Metric
noncomputable section
open GlobalTheory GlobalTheory.Conv
variable (k : ℕ) (hk : k ≠ 0)

theorem GlobalTheory.Conv.coe_expandConv (g : convSeries) :
    (expandConv k hk g : ℂ⟦X⟧) = PowerSeries.expand k hk g := by sorry

attribute [defeq] GlobalTheory.Conv.coe_expandConv
