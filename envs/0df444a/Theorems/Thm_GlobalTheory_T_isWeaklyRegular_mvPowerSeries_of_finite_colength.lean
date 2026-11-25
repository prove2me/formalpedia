-- Prove2me | Theorems.Thm_GlobalTheory_T_isWeaklyRegular_mvPowerSeries_of_finite_colength
-- name    : GlobalTheory.T.isWeaklyRegular_mvPowerSeries_of_finite_colength
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:11:17.288951+00:00
-- url     : https://prove2.me/theorems/20abf389-c435-44de-9dff-ebd4f08cee62
-- title:
--   T: is Weakly Regular mv Power Series of finite colength
-- statement:
--   The T construction uses the is Weakly Regular mv Power Series of finite colength property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsWeaklyRegularMvPowerSeriesOfFiniteColengthStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsWeaklyRegularMvPowerSeriesOfFiniteColengthStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsWeaklyRegularMvPowerSeriesOfFiniteColength
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsWeaklyRegularMvPowerSeriesOfFiniteColengthStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isWeaklyRegular_mvPowerSeries_of_finite_colength : ∀ (k : Type) [Field k] (σ : Type) [Finite σ] (n : ℕ) (e : Fin n ≃ σ) (f : σ → MvPowerSeries σ k), (∀ j, MvPowerSeries.constantCoeff (f j) = 0) → (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤ Ideal.span (Set.range f)) → RingTheory.Sequence.IsWeaklyRegular (MvPowerSeries σ k) (List.ofFn fun i => f (e i)) := by sorry
