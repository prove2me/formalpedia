-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_VolumeFlatSection_mem_parahoric
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.mem_parahoric
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:34.026315+00:00
-- url     : https://prove2.me/theorems/80222654-0409-51c8-932c-f88c2d5b234e
-- title:
--   Volume Flat Section: mem parahoric
-- statement:
--   The Volume Flat Section construction uses the mem parahoric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/VolumeFlatSection.lean#L26-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/VolumeFlatSection.lean#L26-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_VolumeFlatSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling
open scoped NNReal
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']
variable {k A D D'}

theorem GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.mem_parahoric {g : GL (A ⊕ D) k} : g ∈ parahoric k A D ↔
    g ∈ KO k (A ⊕ D) ∧ ∀ i j, valuation k (g.1 (.inr i) (.inl j)) < 1 := by sorry
