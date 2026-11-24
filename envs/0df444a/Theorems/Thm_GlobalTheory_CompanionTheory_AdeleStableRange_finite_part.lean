-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdeleStableRange_finite_part
-- name    : GlobalTheory.CompanionTheory.AdeleStableRange.finite_part
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:16:39.722864+00:00
-- url     : https://prove2.me/theorems/70675e7e-f6e2-40fc-bf96-d4fba64bc8c3
-- title:
--   Adele Stable Range: finite part
-- statement:
--   The Adele Stable Range construction uses the finite part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdeleRingStableRangeOne.lean#L59-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdeleRingStableRangeOne.lean#L59-L77

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

theorem GlobalTheory.CompanionTheory.AdeleStableRange.finite_part (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (a b : FiniteAdeleRing R K) (hab : IsCoprime a b) :
    ∃ t : FiniteAdeleRing R K, IsUnit (a + t * b) := by sorry
