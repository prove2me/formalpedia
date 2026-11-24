-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdeleStableRange_infinite_part
-- name    : GlobalTheory.CompanionTheory.AdeleStableRange.infinite_part
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:16:35.652216+00:00
-- url     : https://prove2.me/theorems/aa2d4706-460f-47b7-af79-9a243ab7e201
-- title:
--   Adele Stable Range: infinite part
-- statement:
--   The Adele Stable Range construction uses the infinite part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdeleRingStableRangeOne.lean#L79-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdeleRingStableRangeOne.lean#L79-L85

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

theorem GlobalTheory.CompanionTheory.AdeleStableRange.infinite_part (K : Type*) [Field K] [NumberField K] (a b : InfiniteAdeleRing K)
    (hab : IsCoprime a b) : ∃ t : InfiniteAdeleRing K, IsUnit (a + t * b) := by sorry
