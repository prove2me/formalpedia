-- Prove2me | Theorems.Thm_GlobalTheory_Conv_coe_expandConvLaurent
-- name    : GlobalTheory.Conv.coe_expandConvLaurent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:30.382809+00:00
-- url     : https://prove2.me/theorems/8f6f05d1-7f41-4c86-bf30-55eb2e194912
-- title:
--   Conv: coe expand Conv Laurent
-- statement:
--   The Conv construction uses the coe expand Conv Laurent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemPuncturedRingIffPowerSeriesPart.lean#L1023-L1024
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemPuncturedRingIffPowerSeriesPart.lean#L1023-L1024

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

theorem GlobalTheory.Conv.coe_expandConvLaurent (f : convLaurent) :
    (expandConvLaurent k hk f : ℂ⸨X⸩) = expandLaurent k hk f := by sorry

attribute [defeq] GlobalTheory.Conv.coe_expandConvLaurent
