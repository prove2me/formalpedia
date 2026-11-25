-- Prove2me | Theorems.Thm_GlobalTheory_sum_sizes_le_ring_polynomial
-- name    : GlobalTheory.sum_sizes_le_ring_polynomial
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:55:52.050793+00:00
-- url     : https://prove2.me/theorems/94cbac7b-b4fa-40e8-8852-f22402a8064f
-- title:
--   Global Theory: sum sizes le ring polynomial
-- statement:
--   The Global Theory construction uses the sum sizes le ring polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/SumSizesLeRingPolynomial.lean#L7-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/SumSizesLeRingPolynomial.lean#L7-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_SumSizesLeRingPolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open GlobalTheory

theorem GlobalTheory.sum_sizes_le_ring_polynomial :
    ∀ (f r m L lE lh lG : ℝ), 8 ≤ f → 62 ≤ r → 2 * m ≤ r → 0 ≤ m → 4 ≤ L → lE ≤ 2 * L → 0 ≤ lE →
      log f ≤ L → lh ≤ f * lE + 2 * f * log (1 + f * lE) → lG ≤ f * r ^ 2 * (18 * L + 2) →
      lG + (m + 5) * lh + (4 * f + 20) * (21 * L) + 100 * L
        ≤ 19 * f * r ^ 2 * L + 198 * f ^ 2 * L := by sorry
