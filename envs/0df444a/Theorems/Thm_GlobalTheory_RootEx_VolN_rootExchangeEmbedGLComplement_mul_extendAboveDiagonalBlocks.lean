-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_VolN_rootExchangeEmbedGLComplement_mul_extendAboveDiagonalBlocks
-- name    : GlobalTheory.RootEx.VolN.rootExchangeEmbedGLComplement_mul_extendAboveDiagonalBlocks
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:29:20.959557+00:00
-- url     : https://prove2.me/theorems/aa8d908d-68a7-4253-bb28-efdd85b19003
-- title:
--   Vol N: root Exchange Embed GLComplement mul extend Above Diagonal Blocks
-- statement:
--   The Vol N construction uses the root Exchange Embed GLComplement mul extend Above Diagonal Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L202-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L202-L221

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.VolN
open GlobalTheory.RootEx.Model
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.RootEx.VolN.rootExchangeEmbedGLComplement_mul_extendAboveDiagonalBlocks (p : ℕ) (x : GL n k) (e : Ix n c p → k) :
    (embX c x).val * ext0 (Up n c p) e = ext0 (Up n c p) ((lm (Up n c p) (embX c x).val).mulVec e) := by sorry
