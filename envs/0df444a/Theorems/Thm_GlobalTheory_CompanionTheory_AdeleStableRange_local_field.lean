-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdeleStableRange_local_field
-- name    : GlobalTheory.CompanionTheory.AdeleStableRange.local_field
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:16:24.599447+00:00
-- url     : https://prove2.me/theorems/711e345f-373a-4ce6-a2e3-dc9266b6f4a0
-- title:
--   Adele Stable Range: local field
-- statement:
--   The Adele Stable Range construction uses the local field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdeleRingStableRangeOne.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdeleRingStableRangeOne.lean#L49-L57

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

theorem GlobalTheory.CompanionTheory.AdeleStableRange.local_field {K : Type*} [Field K] (a b x y : K) (h : x * a + y * b = 1) :
    ∃ t : K, IsUnit (a + t * b) := by sorry
