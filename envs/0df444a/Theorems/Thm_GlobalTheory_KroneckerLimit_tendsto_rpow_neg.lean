-- Prove2me | Theorems.Thm_GlobalTheory_KroneckerLimit_tendsto_rpow_neg
-- name    : GlobalTheory.KroneckerLimit.tendsto_rpow_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:21.45871+00:00
-- url     : https://prove2.me/theorems/9cf5429d-7625-4409-acea-d165b4c45b5d
-- title:
--   Kronecker Limit: tendsto rpow neg
-- statement:
--   The Kronecker Limit construction uses the tendsto rpow neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoRealEisensteinSubPole.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoRealEisensteinSubPole.lean#L38-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Real
open GlobalTheory GlobalTheory.KroneckerLimit

theorem GlobalTheory.KroneckerLimit.tendsto_rpow_neg {r : ℝ} (hr : 0 < r) :
    Tendsto (fun s : ℝ => r ^ (-s)) (𝓝[>] 1) (𝓝 (r ^ (-1 : ℝ))) := by sorry
