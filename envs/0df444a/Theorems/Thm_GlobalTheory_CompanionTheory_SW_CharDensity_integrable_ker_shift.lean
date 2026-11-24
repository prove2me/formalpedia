-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_integrable_ker_shift
-- name    : GlobalTheory.CompanionTheory.SW.CharDensity.integrable_ker_shift
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:02:14.503059+00:00
-- url     : https://prove2.me/theorems/567e672f-bae8-4b6b-ac04-b637cc6997dc
-- title:
--   Char Density: integrable ker shift
-- statement:
--   The Char Density construction uses the integrable ker shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SchurFunctionCompactSupportModuloUnipotent.lean#L183-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SchurFunctionCompactSupportModuloUnipotent.lean#L183-L189

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

theorem GlobalTheory.CompanionTheory.SW.CharDensity.integrable_ker_shift (μ : Measure V) [IsFiniteMeasure μ] {b : ℝ} (hb : 0 < b) (y : V) :
    Integrable (fun z => ker b (z - y)) μ := by sorry
