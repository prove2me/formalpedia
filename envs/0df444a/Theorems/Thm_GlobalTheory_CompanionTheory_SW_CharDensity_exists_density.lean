-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_exists_density
-- name    : GlobalTheory.CompanionTheory.SW.CharDensity.exists_density
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:03:05.796814+00:00
-- url     : https://prove2.me/theorems/489df6fb-51ee-442e-bd54-269ee94bbfd4
-- title:
--   Char Density: exists density
-- statement:
--   The Char Density construction uses the exists density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SchurFunctionCompactSupportModuloUnipotent.lean#L231-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SchurFunctionCompactSupportModuloUnipotent.lean#L231-L268

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

theorem GlobalTheory.CompanionTheory.SW.CharDensity.exists_density (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (phi μ) volume) :
    ∃ D : V → ℝ, Continuous D ∧ (∀ y, 0 ≤ D y) ∧ (∀ y, (D y : ℂ) = dens μ y) ∧
      μ = (volume : Measure V).withDensity (fun y => ENNReal.ofReal (D y)) := by sorry
