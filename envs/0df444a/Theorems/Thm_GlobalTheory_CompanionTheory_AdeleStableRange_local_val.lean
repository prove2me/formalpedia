-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdeleStableRange_local_val
-- name    : GlobalTheory.CompanionTheory.AdeleStableRange.local_val
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:16:37.94615+00:00
-- url     : https://prove2.me/theorems/4c81b815-18a1-43be-b4ba-497ba1e0c49c
-- title:
--   Adele Stable Range: local val
-- statement:
--   The Adele Stable Range construction uses the local val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdeleRingStableRangeOne.lean#L8-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdeleRingStableRangeOne.lean#L8-L47

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

theorem GlobalTheory.CompanionTheory.AdeleStableRange.local_val {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ)
    (a b x y : K) (h : x * a + y * b = 1) :
    ∃ t : K, (t = 0 ∨ t = 1) ∧ a + t * b ≠ 0 ∧
      (w a ≤ 1 → w b ≤ 1 → w x ≤ 1 → w y ≤ 1 → w (a + t * b) = 1) := by sorry
