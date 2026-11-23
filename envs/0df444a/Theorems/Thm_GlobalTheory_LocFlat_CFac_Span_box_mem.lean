-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_box_mem
-- name    : GlobalTheory.LocFlat.CFac.Span.box_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:23.863189+00:00
-- url     : https://prove2.me/theorems/cf7183c1-011a-44dd-b116-af8b673d09ca
-- title:
--   Span: box mem
-- statement:
--   The Span construction uses the box mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SpanSchwartzBruhatProductEqTop.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SpanSchwartzBruhatProductEqTop.lean#L36-L43

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

theorem GlobalTheory.LocFlat.CFac.Span.box_mem {r : Set X × Set Y} (hr : IsBox r) :
    (r.1 ×ˢ r.2).indicator (1 : X × Y → ℂ) ∈ S X Y := by sorry
