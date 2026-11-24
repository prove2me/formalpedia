-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_isClopen_isCompact_mapsPair
-- name    : GlobalTheory.LatPair.isClopen_isCompact_mapsPair
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:58:35.062081+00:00
-- url     : https://prove2.me/theorems/a2f9940f-75c4-439b-964a-75ea7d294cc2
-- title:
--   Lat Pair: is Clopen is Compact maps Pair
-- statement:
--   The Lat Pair construction uses the is Clopen is Compact maps Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactMapsPair.lean#L77-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactMapsPair.lean#L77-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
open SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable [Fintype n] [Fintype n']

theorem GlobalTheory.LatPair.isClopen_isCompact_mapsPair (P : Pair k n') (Q : Pair k n) :
    IsClopen {x : Matrix n n' k | Maps P Q x} ∧ IsCompact {x : Matrix n n' k | Maps P Q x} := by sorry
