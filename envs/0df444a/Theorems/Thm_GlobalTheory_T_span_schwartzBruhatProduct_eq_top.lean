-- Prove2me | Theorems.Thm_GlobalTheory_T_span_schwartzBruhatProduct_eq_top
-- name    : GlobalTheory.T.span_schwartzBruhatProduct_eq_top
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:59:28.068818+00:00
-- url     : https://prove2.me/theorems/f7eca347-e42d-4f4b-9c12-3ce5c54979f9
-- title:
--   T: span schwartz Bruhat Product eq top
-- statement:
--   The T construction uses the span schwartz Bruhat Product eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SpanSchwartzBruhatProductEqTopStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SpanSchwartzBruhatProductEqTopStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SpanSchwartzBruhatProductEqTop
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SpanSchwartzBruhatProductEqTopStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.span_schwartzBruhatProduct_eq_top : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y], Submodule.span ℂ (Set.range fun q : SB X × SB Y => prodSB q.1 q.2) = ⊤ := by sorry
