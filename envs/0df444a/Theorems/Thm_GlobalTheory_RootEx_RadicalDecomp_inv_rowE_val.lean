-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_RadicalDecomp_inv_rowE_val
-- name    : GlobalTheory.RootEx.RadicalDecomp.inv_rowE_val
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:28:19.655527+00:00
-- url     : https://prove2.me/theorems/771cb348-4689-40ab-9889-b121af0a453d
-- title:
--   Radical Decomp: inv row E val
-- statement:
--   The Radical Decomp construction uses the inv row E val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentSubgroupSuccDecomposition.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentSubgroupSuccDecomposition.lean#L27-L28

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

theorem GlobalTheory.RootEx.RadicalDecomp.inv_rowE_val (u : n → k) : ((rowE c p u)⁻¹).val =
    fromBlocks 1 0 (-(Matrix.of fun (l : Fin c) s => if l.val + 1 = p then u s else 0)) 1 := by sorry
