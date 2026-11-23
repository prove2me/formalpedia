-- Prove2me | Theorems.Thm_GlobalTheory_KroneckerLimit_rowSum_bound
-- name    : GlobalTheory.KroneckerLimit.rowSum_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:17:24.194511+00:00
-- url     : https://prove2.me/theorems/13a74d29-ce30-43b4-af14-7cf7459eb2ae
-- title:
--   Kronecker Limit: row Sum bound
-- statement:
--   The Kronecker Limit construction uses the row Sum bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoRealEisensteinSubPole.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoRealEisensteinSubPole.lean#L11-L23

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

theorem GlobalTheory.KroneckerLimit.rowSum_bound (a : ℝ) {Y s : ℝ} (hY : 0 < Y) (hs : 1 ≤ s) :
    Summable (fun n : ℤ => ((a + n) ^ 2 + Y ^ 2) ^ (-s)) ∧
      |rowSum a Y s - betaConst s * Y ^ (1 - 2 * s)| ≤ (Y ^ 2) ^ (-s) := by sorry
