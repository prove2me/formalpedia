-- Prove2me | Theorems.Thm_GlobalTheory_gradedSeries_regroup
-- name    : GlobalTheory.gradedSeries_regroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:50.233881+00:00
-- url     : https://prove2.me/theorems/f102d1cd-131a-4e17-81df-ae8afd1e767f
-- title:
--   Global Theory: graded Series regroup
-- statement:
--   The Global Theory construction uses the graded Series regroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/GradedSeriesContinuationDominated.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/GradedSeriesContinuationDominated.lean#L7-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GradedSeriesContinuationDominated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Metric Set
open GlobalTheory

theorem GlobalTheory.gradedSeries_regroup {ι : Type} (deg : ι → ℕ) (c : ι → ℂ) (x s : ℂ)
    (hs : HasSum (fun i => c i * x ^ deg i) s) :
    HasSum (fun k => (∑' i : deg ⁻¹' {k}, c i) * x ^ k) s := by sorry
