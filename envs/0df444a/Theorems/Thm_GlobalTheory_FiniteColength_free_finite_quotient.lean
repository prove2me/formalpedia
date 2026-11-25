-- Prove2me | Theorems.Thm_GlobalTheory_FiniteColength_free_finite_quotient
-- name    : GlobalTheory.FiniteColength.free_finite_quotient
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:44:26.634623+00:00
-- url     : https://prove2.me/theorems/395cee44-e7e6-5a30-bf9c-068e1feb70ef
-- title:
--   Finite Colength: free finite quotient
-- statement:
--   The Finite Colength construction uses the free finite quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MapMaximalIdealEqKerMapResidue.lean#L25-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MapMaximalIdealEqKerMapResidue.lean#L25-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsWeaklyRegularMvPowerSeriesOfFiniteColengthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatMvPowerSeriesOfIsNoetherianRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatQuotientWeaklyRegularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MapMaximalIdealEqKerMapResidue
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.FiniteColength

theorem GlobalTheory.FiniteColength.free_finite_quotient : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T], IsAdicComplete (maximalIdeal T) T → ∀ (σ : Type) [Finite σ] (n : ℕ) (e : Fin n ≃ σ) (f : Fin n → MvPowerSeries σ T), (∀ j, MvPowerSeries.constantCoeff (f j) = 0) → (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField T))) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue T) (f j))) → Module.Free T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) ∧ Module.Finite T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) := by sorry
