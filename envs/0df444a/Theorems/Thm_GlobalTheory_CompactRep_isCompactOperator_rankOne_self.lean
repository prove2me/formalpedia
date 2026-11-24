-- Prove2me | Theorems.Thm_GlobalTheory_CompactRep_isCompactOperator_rankOne_self
-- name    : GlobalTheory.CompactRep.isCompactOperator_rankOne_self
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:16:23.419345+00:00
-- url     : https://prove2.me/theorems/a4beb447-569b-40ef-876d-da57e5ea00ec
-- title:
--   Compact Rep: is Compact Operator rank One self
-- statement:
--   The Compact Rep construction uses the is Compact Operator rank One self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CompactUnitaryFiniteInvariantSubspace.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CompactUnitaryFiniteInvariantSubspace.lean#L21-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CompactUnitaryFiniteInvariantSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory InnerProductSpace
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompactRep
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem GlobalTheory.CompactRep.isCompactOperator_rankOne_self (w : H) : IsCompactOperator (rankOne ℂ w w) := by sorry
