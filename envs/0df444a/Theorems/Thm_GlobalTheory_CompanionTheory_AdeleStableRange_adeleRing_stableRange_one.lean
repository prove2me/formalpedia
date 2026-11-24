-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdeleStableRange_adeleRing_stableRange_one
-- name    : GlobalTheory.CompanionTheory.AdeleStableRange.adeleRing_stableRange_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:16:31.296554+00:00
-- url     : https://prove2.me/theorems/ca445387-7f57-4fe8-9a8f-5a215c166cd8
-- title:
--   Adele Stable Range: adele Ring stable Range one
-- statement:
--   The Adele Stable Range construction uses the adele Ring stable Range one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdeleRingStableRangeOne.lean#L87-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdeleRingStableRangeOne.lean#L87-L93

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdeleRingStableRangeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdeleStableRange

theorem GlobalTheory.CompanionTheory.AdeleStableRange.adeleRing_stableRange_one : ∀ (F : Type) [Field F] [NumberField F] (a b : AdeleRing (𝓞 F) F),
    IsCoprime a b → ∃ t, IsUnit (a + t * b) := by sorry
