-- Prove2me | Theorems.Thm_GlobalTheory_PosDefFT_integral_prod_nonneg
-- name    : GlobalTheory.PosDefFT.integral_prod_nonneg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:49:48.903661+00:00
-- url     : https://prove2.me/theorems/b51445ec-0532-436b-b2cd-9d3e4e462e09
-- title:
--   Pos Def FT: integral prod nonneg
-- statement:
--   The Pos Def FT construction uses the integral prod nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntegralNonnegOfSums.lean#L7-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntegralNonnegOfSums.lean#L7-L51

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

theorem GlobalTheory.PosDefFT.integral_prod_nonneg (ψ : ℝ → ℂ) (hc : Continuous ψ) (C : ℝ) (hb : ∀ s, ‖ψ s‖ ≤ C)
    (hp : ∀ (k : ℕ) (t : Fin k → ℝ), 0 ≤ ∑ i, ∑ j, ψ (t j - t i))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 ≤ ∫ p : ℝ × ℝ, ψ (p.2 - p.1) ∂(μ.prod μ) := by sorry
