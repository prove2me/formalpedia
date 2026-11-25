-- Prove2me | Theorems.Thm_GlobalTheory_isWeaklyRegular_mvPowerSeries_of_pow_le
-- name    : GlobalTheory.isWeaklyRegular_mvPowerSeries_of_pow_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:06:15.97366+00:00
-- url     : https://prove2.me/theorems/767eaae3-6825-4ee7-b085-dff94b8f899e
-- title:
--   Global Theory: is Weakly Regular mv Power Series of pow le
-- statement:
--   The Global Theory construction uses the is Weakly Regular mv Power Series of pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsWeaklyRegularMvPowerSeriesOfFiniteColength.lean#L9-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsWeaklyRegularMvPowerSeriesOfFiniteColength.lean#L9-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsWeaklyRegularMvPowerSeriesOfFiniteColength
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

theorem GlobalTheory.isWeaklyRegular_mvPowerSeries_of_pow_le :
    ∀ (k : Type) [Field k] (σ : Type) [Finite σ] (n : ℕ) (e : Fin n ≃ σ)
      (f : σ → MvPowerSeries σ k), (∀ j, MvPowerSeries.constantCoeff (f j) = 0) →
      (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤
        Ideal.span (Set.range f)) →
      RingTheory.Sequence.IsWeaklyRegular (MvPowerSeries σ k) (List.ofFn fun i => f (e i)) := by sorry
