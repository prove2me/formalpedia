-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_F_mem
-- name    : GlobalTheory.LocFlat.CFac.Span.F_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:12:10.962735+00:00
-- url     : https://prove2.me/theorems/1e00fc07-b9e0-423c-8b02-c80e383c1354
-- title:
--   Span: F mem
-- statement:
--   The Span construction uses the F mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SpanSchwartzBruhatProductEqTop.lean#L83-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SpanSchwartzBruhatProductEqTop.lean#L83-L109

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

theorem GlobalTheory.LocFlat.CFac.Span.F_mem (F : X × Y → ℂ) : ∀ L : List (Set X × Set Y),
    (∀ r ∈ L, IsBox r ∧ ∃ c : ℂ, ∀ p ∈ r.1 ×ˢ r.2, F p = c) → (U L).indicator F ∈ S X Y := by sorry
