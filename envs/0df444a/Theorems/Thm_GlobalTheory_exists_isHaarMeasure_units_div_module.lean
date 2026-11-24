-- Prove2me | Theorems.Thm_GlobalTheory_exists_isHaarMeasure_units_div_module
-- name    : GlobalTheory.exists_isHaarMeasure_units_div_module
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:16.158069+00:00
-- url     : https://prove2.me/theorems/239142c8-11c0-4949-9b61-ddfb0fb481be
-- title:
--   Global Theory: exists is Haar Measure units div module
-- statement:
--   The Global Theory construction uses the exists is Haar Measure units div module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ContinuousDistribHaarCharUnitsOfCompactOpen.lean#L44-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ContinuousDistribHaarCharUnitsOfCompactOpen.lean#L44-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousDistribHaarCharUnitsOfCompactOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open scoped Pointwise
open GlobalTheory

theorem GlobalTheory.exists_isHaarMeasure_units_div_module : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [IsOpenUnits R] [MeasurableSpace R] [BorelSpace R] [BorelSpace Rˣ] (μ : Measure R), μ.IsAddHaarMeasure → (∃ S : Set R, IsOpen S ∧ IsCompact S ∧ S.Nonempty) → ∃ μ' : Measure Rˣ, μ'.IsHaarMeasure ∧ ∀ (g δ : R → ℂ), (∀ u : Rˣ, δ u = ((distribHaarChar R u : ℝ) : ℂ)) → ∀ T : Set Rˣ, MeasurableSet T → ∫ u in T, g u ∂μ' = ∫ t in Units.val '' T, g t * (δ t)⁻¹ ∂μ := by sorry
