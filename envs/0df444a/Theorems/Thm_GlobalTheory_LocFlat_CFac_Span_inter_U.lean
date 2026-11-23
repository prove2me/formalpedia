-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_CFac_Span_inter_U
-- name    : GlobalTheory.LocFlat.CFac.Span.inter_U
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:32.679812+00:00
-- url     : https://prove2.me/theorems/dedc830b-d91e-4515-994d-da4cd8defea9
-- title:
--   Span: inter U
-- statement:
--   The Span construction uses the inter U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SpanSchwartzBruhatProductEqTop.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SpanSchwartzBruhatProductEqTop.lean#L50-L58

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

theorem GlobalTheory.LocFlat.CFac.Span.inter_U (r : Set X × Set Y) (L : List (Set X × Set Y)) :
    r.1 ×ˢ r.2 ∩ U L = U (L.map fun s => (r.1 ∩ s.1, r.2 ∩ s.2)) := by sorry
