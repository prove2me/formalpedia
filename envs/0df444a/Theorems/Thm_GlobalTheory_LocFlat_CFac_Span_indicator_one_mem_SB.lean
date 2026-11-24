-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_indicator_one_mem_SB
-- name    : GlobalTheory.LocFlat.CFac.Span.indicator_one_mem_SB
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:12:33.300852+00:00
-- url     : https://prove2.me/theorems/fb9bcf5d-fc09-469a-9aba-fe352d691e26
-- title:
--   Span: indicator one mem SB
-- statement:
--   The Span construction uses the indicator one mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SpanSchwartzBruhatProductEqTop.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SpanSchwartzBruhatProductEqTop.lean#L20-L22

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

theorem GlobalTheory.LocFlat.CFac.Span.indicator_one_mem_SB {Z : Type} [TopologicalSpace Z] {W : Set Z} (hc : IsCompact W)
    (hW : IsClopen W) : W.indicator (1 : Z → ℂ) ∈ SB Z := by sorry
