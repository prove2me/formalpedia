-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_tendsto_smoothed
-- name    : GlobalTheory.CompanionTheory.SW.CharDensity.tendsto_smoothed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:54.104974+00:00
-- url     : https://prove2.me/theorems/e32eca05-59d1-438a-937c-53c02455cbd2
-- title:
--   Char Density: tendsto smoothed
-- statement:
--   The Char Density construction uses the tendsto smoothed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SchurFunctionCompactSupportModuloUnipotent.lean#L140-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SchurFunctionCompactSupportModuloUnipotent.lean#L140-L168

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CharDensity
open scoped FourierTransform
open Filter
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem GlobalTheory.CompanionTheory.SW.CharDensity.tendsto_smoothed (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (phi μ) volume)
    (y : V) :
    Tendsto (fun n : ℕ => ((∫ z, ker (bn n) (z - y) ∂μ : ℝ) : ℂ)) atTop (𝓝 (dens μ y)) := by sorry
