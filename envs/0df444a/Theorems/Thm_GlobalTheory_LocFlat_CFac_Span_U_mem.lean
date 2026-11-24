-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_U_mem
-- name    : GlobalTheory.LocFlat.CFac.Span.U_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:12:20.132963+00:00
-- url     : https://prove2.me/theorems/86bc4906-2322-413a-890f-1bc0e6b196a5
-- title:
--   Span: U mem
-- statement:
--   The Span construction uses the U mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SpanSchwartzBruhatProductEqTop.lean#L60-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SpanSchwartzBruhatProductEqTop.lean#L60-L81

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

theorem GlobalTheory.LocFlat.CFac.Span.U_mem : ∀ (n : ℕ) (L : List (Set X × Set Y)), L.length ≤ n → (∀ r ∈ L, IsBox r) →
    (U L).indicator (1 : X × Y → ℂ) ∈ S X Y := by sorry
