-- Prove2me | Theorems.Thm_GlobalTheory_CompactRep_continuous_rankOne_self
-- name    : GlobalTheory.CompactRep.continuous_rankOne_self
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:16:54.61905+00:00
-- url     : https://prove2.me/theorems/0072c735-273f-4c70-ace4-1a7840296e0a
-- title:
--   Compact Rep: continuous rank One self
-- statement:
--   The Compact Rep construction uses the continuous rank One self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CompactUnitaryFiniteInvariantSubspace.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CompactUnitaryFiniteInvariantSubspace.lean#L11-L19

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

theorem GlobalTheory.CompactRep.continuous_rankOne_self : Continuous fun w : H => rankOne ℂ w w := by sorry
