-- Prove2me | Theorems.Thm_GlobalTheory_eLpNorm_two_le_ofReal_sqrt_of_integral_le
-- name    : GlobalTheory.eLpNorm_two_le_ofReal_sqrt_of_integral_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:47.248637+00:00
-- url     : https://prove2.me/theorems/6b2e9ff7-0c7d-494d-95bb-d763a1d4c18b
-- title:
--   Global Theory: e Lp Norm two le of Real sqrt of integral le
-- statement:
--   The Global Theory construction uses the e Lp Norm two le of Real sqrt of integral le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MemLpTwoAndTendstoOfCauchyOfAeTendsto.lean#L6-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MemLpTwoAndTendstoOfCauchyOfAeTendsto.lean#L6-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MemLpTwoAndTendstoOfCauchyOfAeTendsto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory

theorem GlobalTheory.eLpNorm_two_le_ofReal_sqrt_of_integral_le {X : Type} [MeasurableSpace X] {μ : Measure X} {E : Type}
    [NormedAddCommGroup E] {f : X → E} (hf : MemLp f 2 μ) {c : ℝ}
    (h : ∫ x, ‖f x‖ ^ 2 ∂μ ≤ c) : eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt c) := by sorry
