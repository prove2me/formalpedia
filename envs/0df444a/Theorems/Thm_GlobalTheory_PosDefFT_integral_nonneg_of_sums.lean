-- Prove2me | Theorems.Thm_GlobalTheory_PosDefFT_integral_nonneg_of_sums
-- name    : GlobalTheory.PosDefFT.integral_nonneg_of_sums
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:49:30.655117+00:00
-- url     : https://prove2.me/theorems/89123331-0fed-4763-8efe-26be839857a8
-- title:
--   Pos Def FT: integral nonneg of sums
-- statement:
--   The Pos Def FT construction uses the integral nonneg of sums property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntegralNonnegOfSums.lean#L53-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntegralNonnegOfSums.lean#L53-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralNonnegOfSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.PosDefFT

theorem GlobalTheory.PosDefFT.integral_nonneg_of_sums (ψ : ℝ → ℂ) (hc : Continuous ψ) (C : ℝ) (hb : ∀ s, ‖ψ s‖ ≤ C)
    (hi : Integrable ψ)
    (hp : ∀ (k : ℕ) (t : Fin k → ℝ), 0 ≤ ∑ i, ∑ j, ψ (t j - t i)) :
    0 ≤ ∫ s, ψ s := by sorry
