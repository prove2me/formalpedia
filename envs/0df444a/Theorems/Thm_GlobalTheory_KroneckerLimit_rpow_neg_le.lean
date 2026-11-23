-- Prove2me | Theorems.Thm_GlobalTheory_KroneckerLimit_rpow_neg_le
-- name    : GlobalTheory.KroneckerLimit.rpow_neg_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:14.506254+00:00
-- url     : https://prove2.me/theorems/4d3dd362-6077-4981-896f-0149c9484792
-- title:
--   Kronecker Limit: rpow neg le
-- statement:
--   The Kronecker Limit construction uses the rpow neg le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoRealEisensteinSubPole.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoRealEisensteinSubPole.lean#L25-L33

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

theorem GlobalTheory.KroneckerLimit.rpow_neg_le {r s : ℝ} (hr : 0 < r) (h1 : 1 ≤ s) (h2 : s ≤ 2) :
    r ^ (-s) ≤ r ^ (-1 : ℝ) + r ^ (-2 : ℝ) := by sorry
