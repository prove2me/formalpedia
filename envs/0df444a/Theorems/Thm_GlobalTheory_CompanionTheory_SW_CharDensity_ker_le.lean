-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_ker_le
-- name    : GlobalTheory.CompanionTheory.SW.CharDensity.ker_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:02:26.488132+00:00
-- url     : https://prove2.me/theorems/753870c0-5a99-4713-98b8-466bfbf857a5
-- title:
--   Char Density: ker le
-- statement:
--   The Char Density construction uses the ker le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SchurFunctionCompactSupportModuloUnipotent.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SchurFunctionCompactSupportModuloUnipotent.lean#L43-L50

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

theorem GlobalTheory.CompanionTheory.SW.CharDensity.ker_le {b : ℝ} (hb : 0 < b) (w : V) :
    ker b w ≤ (Real.pi / b) ^ ((Module.finrank ℝ V : ℝ) / 2) := by sorry
