-- Prove2me | Theorems.Thm_GlobalTheory_T_contDensity_eq_fibre_measure_of_compact_open
-- name    : GlobalTheory.T.contDensity_eq_fibre_measure_of_compact_open
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:32:04.540461+00:00
-- url     : https://prove2.me/theorems/156d5107-29eb-49f2-bc7c-e40951f796d6
-- title:
--   T: cont Density eq fibre measure of compact open
-- statement:
--   The T construction uses the cont Density eq fibre measure of compact open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ContDensityOnEqFibreMassStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ContDensityOnEqFibreMassStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ContDensityOnEqFibreMass
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ContDensityOnEqFibreMassStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.contDensity_eq_fibre_measure_of_compact_open : ∀ (K V : Type) [NormedField K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [TopologicalSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → ∀ (fib : K → Measure V), IsFibreFamily μ q id Set.univ ν {t | t ≠ 0} fib → ∀ (L : Set V), IsCompact L → IsOpen L → ∀ g : K → ℂ, IsContDensityOn μ q id ν {t | t ≠ 0} (L.indicator 1) g → ∀ t : K, t ≠ 0 → g t = (((fib t L).toReal : ℝ) : ℂ) := by sorry
