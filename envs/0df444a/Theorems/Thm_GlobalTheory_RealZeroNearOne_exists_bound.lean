-- Prove2me | Theorems.Thm_GlobalTheory_RealZeroNearOne_exists_bound
-- name    : GlobalTheory.RealZeroNearOne.exists_bound
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:17:13.67037+00:00
-- url     : https://prove2.me/theorems/4a1e6e5f-50f4-4d0d-aec6-b0617e014e4f
-- title:
--   Real Zero Near One: exists bound
-- statement:
--   The Real Zero Near One construction uses the exists bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/OrderNeTop.lean#L33-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/OrderNeTop.lean#L33-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivDirichletLFunctionLocalZeroSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegSumLogDerivNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_OrderNeTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.RealZeroNearOne

theorem GlobalTheory.RealZeroNearOne.exists_bound : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ ≠ 1 → ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ T : Finset ℝ,
    (∀ β ∈ T, 2 / 3 ≤ β ∧ LFunction χ β = 0) →
    -(deriv (LFunction χ) σ / LFunction χ σ).re ≤ C * Real.log (2 * q)
      - ∑ β ∈ T, (analyticOrderNatAt (LFunction χ) β : ℝ) / (σ - β) := by sorry
