-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryChart_unitary_list_prod
-- name    : GlobalTheory.UnitaryChart.unitary_list_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:08:39.731404+00:00
-- url     : https://prove2.me/theorems/852d09f8-8c45-496b-9943-94627d3606f0
-- title:
--   Unitary Chart: unitary list prod
-- statement:
--   The Unitary Chart construction uses the unitary list prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupSecondKindCoordinatesNearOne.lean#L29-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupSecondKindCoordinatesNearOne.lean#L29-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupSecondKindCoordinatesNearOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.UnitaryChart
open Topology Filter

theorem GlobalTheory.UnitaryChart.unitary_list_prod {E : Type} [Ring E] (σ : E → E) (hm : ∀ a b, σ (a * b) = σ b * σ a)
    (h1 : σ 1 = 1) (l : List E) (hl : ∀ u ∈ l, σ u * u = 1 ∧ u * σ u = 1) :
    σ l.prod * l.prod = 1 ∧ l.prod * σ l.prod = 1 := by sorry
