-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_exists_compact_clopen
-- name    : GlobalTheory.LocFlat.CFac.Span.exists_compact_clopen
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:12:14.885806+00:00
-- url     : https://prove2.me/theorems/7e05be5c-b01f-4111-b472-bb8b89cd80fa
-- title:
--   Span: exists compact clopen
-- statement:
--   The Span construction uses the exists compact clopen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SpanSchwartzBruhatProductEqTop.lean#L111-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SpanSchwartzBruhatProductEqTop.lean#L111-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SpanSchwartzBruhatProductEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.CFac GlobalTheory.LocFlat.CFac.Span
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem GlobalTheory.LocFlat.CFac.Span.exists_compact_clopen [LocallyCompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {x : X} {O : Set X} (hO : IsOpen O) (hx : x ∈ O) :
    ∃ V, IsCompact V ∧ IsClopen V ∧ x ∈ V ∧ V ⊆ O := by sorry
