-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_VolN_det_block_fromBlocks
-- name    : GlobalTheory.RootEx.VolN.det_block_fromBlocks
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:49.820715+00:00
-- url     : https://prove2.me/theorems/005c1a3c-13ad-4e4d-bd73-58f8527b79b4
-- title:
--   Vol N: det block from Blocks
-- statement:
--   The Vol N construction uses the det block from Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L114-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L114-L138

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
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.RootEx.VolN.det_block_fromBlocks {n t : Type} [Fintype n] [DecidableEq n] [Fintype t] [DecidableEq t]
    (x : Matrix n n k) (Q : n ⊕ t → Prop) [DecidablePred Q] (q : Prop) [Decidable q]
    (hQ : ∀ a, Q (Sum.inl a) ↔ q) :
    ((fromBlocks x 0 0 1 : Matrix (n ⊕ t) (n ⊕ t) k).toSquareBlockProp Q).det = if q then x.det else 1 := by sorry
