-- Prove2me | Theorems.Thm_GlobalTheory_KroneckerLimit_summable_sq_rpow
-- name    : GlobalTheory.KroneckerLimit.summable_sq_rpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:16.438019+00:00
-- url     : https://prove2.me/theorems/0f83104b-743e-4b26-936b-ce9da0fdb9b4
-- title:
--   Kronecker Limit: summable sq rpow
-- statement:
--   The Kronecker Limit construction uses the summable sq rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoRealEisensteinSubPole.lean#L220-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoRealEisensteinSubPole.lean#L220-L228

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

theorem GlobalTheory.KroneckerLimit.summable_sq_rpow {y s : ℝ} (hy : 0 < y) (hs : 1 ≤ s) :
    Summable fun m : ℕ => (((m + 1) * y) ^ 2) ^ (-s) := by sorry
