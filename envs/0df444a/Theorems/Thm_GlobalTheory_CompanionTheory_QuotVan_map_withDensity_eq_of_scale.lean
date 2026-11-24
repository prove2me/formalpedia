-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QuotVan_map_withDensity_eq_of_scale
-- name    : GlobalTheory.CompanionTheory.QuotVan.map_withDensity_eq_of_scale
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:58:02.24935+00:00
-- url     : https://prove2.me/theorems/73f98d47-2044-4186-8f90-db191c9c8eb7
-- title:
--   Quot Van: map with Density eq of scale
-- statement:
--   The Quot Van construction uses the map with Density eq of scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MapWithDensityEqOfScale.lean#L18-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MapWithDensityEqOfScale.lean#L18-L36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TopoPolish
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MapWithDensityEqOfScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QuotVan

theorem GlobalTheory.CompanionTheory.QuotVan.map_withDensity_eq_of_scale {X : Type*} [MeasurableSpace X] (ρ : Measure X) (S : X → X)
    (hS : Measurable S) (f : X → ℝ≥0∞) (hf : Measurable f) (a : ℝ≥0∞) (ha0 : a ≠ 0) (hat : a ≠ ∞)
    (hρ : ρ.map S = a • ρ) (hfS : ∀ x, f (S x) = a * f x) :
    (ρ.withDensity f).map S = ρ.withDensity f := by sorry
