-- Prove2me | Theorems.Thm_GlobalTheory_pow_span_X_le_and_finite_quotient_of_le_sup_pow_succ
-- name    : GlobalTheory.pow_span_X_le_and_finite_quotient_of_le_sup_pow_succ
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:50:39.202897+00:00
-- url     : https://prove2.me/theorems/6b1c061d-35fa-548c-833c-ad2c62d81302
-- title:
--   Global Theory: pow span X le and finite quotient of le sup pow succ
-- statement:
--   The Global Theory construction uses the pow span X le and finite quotient of le sup pow succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/PowSpanXLeAndFiniteQuotientOfLeSupPowSucc.lean#L8-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/PowSpanXLeAndFiniteQuotientOfLeSupPowSucc.lean#L8-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PowSpanXLeAndFiniteQuotientOfLeSupPowSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.pow_span_X_le_and_finite_quotient_of_le_sup_pow_succ : ∀ (k : Type) [Field k] (σ : Type) [Finite σ] (I : Ideal (MvPowerSeries σ k)) (M : ℕ), Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤ I ⊔ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ (M + 1) → Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤ I ∧ Module.Finite k (MvPowerSeries σ k ⧸ I) := by sorry
