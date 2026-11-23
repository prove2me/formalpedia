-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSICHWMap_hwMap_of_lowSpan
-- name    : GlobalTheory.CompanionTheory.DSICHWMap.hwMap_of_lowSpan
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:06.637777+00:00
-- url     : https://prove2.me/theorems/01f82cf2-2566-4fd6-b09e-39d3995d1c7d
-- title:
--   DSICHWMap: hw Map of low Span
-- statement:
--   The DSICHWMap construction uses the hw Map of low Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HwMapOfLowSpan.lean#L50-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HwMapOfLowSpan.lean#L50-L144

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HwMapOfLowSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICHWMap
open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)
variable {T V : Type} [NormedAddCommGroup T] [InnerProductSpace ℂ T] [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem GlobalTheory.CompanionTheory.DSICHWMap.hwMap_of_lowSpan : LowSpan → HWMap := by sorry
