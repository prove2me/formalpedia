-- Prove2me | Theorems.Thm_GlobalTheory_RestrMeas_normHaar_self
-- name    : GlobalTheory.RestrMeas.normHaar_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:17.155698+00:00
-- url     : https://prove2.me/theorems/7bf09265-0e14-457d-9090-edf12ddda988
-- title:
--   Restr Meas: norm Haar self
-- statement:
--   The Restr Meas construction uses the norm Haar self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L475-L477
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L475-L477

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RestrMeas
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal

theorem GlobalTheory.RestrMeas.normHaar_self {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (K : Subgroup G) (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) :
    normHaar K ho hc K = 1 := by sorry
