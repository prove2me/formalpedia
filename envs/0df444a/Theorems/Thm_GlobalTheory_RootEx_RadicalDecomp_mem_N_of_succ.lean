-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_RadicalDecomp_mem_N_of_succ
-- name    : GlobalTheory.RootEx.RadicalDecomp.mem_N_of_succ
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:28:45.237821+00:00
-- url     : https://prove2.me/theorems/09568886-492f-4c82-95b9-3af320e7206b
-- title:
--   Radical Decomp: mem N of succ
-- statement:
--   The Radical Decomp construction uses the mem N of succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentSubgroupSuccDecomposition.lean#L12-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentSubgroupSuccDecomposition.lean#L12-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentSubgroupSuccDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.RadicalDecomp
open GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem GlobalTheory.RootEx.RadicalDecomp.mem_N_of_succ {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c (p + 1))
    (h0 : ∀ (l : Fin c) (s : n), l.val + 1 = p → g.val (Sum.inr l) (Sum.inl s) = 0) :
    g ∈ N k n c p := by sorry
