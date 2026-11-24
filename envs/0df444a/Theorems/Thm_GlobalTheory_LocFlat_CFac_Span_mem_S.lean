-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_mem_S
-- name    : GlobalTheory.LocFlat.CFac.Span.mem_S
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:12:28.462123+00:00
-- url     : https://prove2.me/theorems/d5a32f2c-b0d9-4026-b508-b9de772e2d9d
-- title:
--   Span: mem S
-- statement:
--   The Span construction uses the mem S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SpanSchwartzBruhatProductEqTop.lean#L120-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SpanSchwartzBruhatProductEqTop.lean#L120-L147

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

theorem GlobalTheory.LocFlat.CFac.Span.mem_S [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
    [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
    (F : X × Y → ℂ) (hF : F ∈ SB (X × Y)) : F ∈ S X Y := by sorry
