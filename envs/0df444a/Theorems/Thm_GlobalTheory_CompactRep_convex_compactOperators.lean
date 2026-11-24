-- Prove2me | Theorems.Thm_GlobalTheory_CompactRep_convex_compactOperators
-- name    : GlobalTheory.CompactRep.convex_compactOperators
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:16:13.672785+00:00
-- url     : https://prove2.me/theorems/fd88c1ae-7d4f-4d93-9c40-5215a2d56930
-- title:
--   Compact Rep: convex compact Operators
-- statement:
--   The Compact Rep construction uses the convex compact Operators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CompactUnitaryFiniteInvariantSubspace.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CompactUnitaryFiniteInvariantSubspace.lean#L26-L27

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

theorem GlobalTheory.CompactRep.convex_compactOperators : Convex ℝ {f : H →L[ℂ] H | IsCompactOperator f} := by sorry
