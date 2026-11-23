-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_VolN_mul_matrixExtendSelectedEntriesByZero_apply
-- name    : GlobalTheory.RootEx.VolN.mul_matrixExtendSelectedEntriesByZero_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:06.788106+00:00
-- url     : https://prove2.me/theorems/9024dc13-4179-4b1a-9e59-401d1d7993e6
-- title:
--   Vol N: mul matrix Extend Selected Entries By Zero apply
-- statement:
--   The Vol N construction uses the mul matrix Extend Selected Entries By Zero apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L39-L45

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

theorem GlobalTheory.RootEx.VolN.mul_matrixExtendSelectedEntriesByZero_apply (P : ι → ι → Prop) [DecidableRel P] [F : Fintype {rs : ι × ι // P rs.1 rs.2}] (h : Matrix ι ι k)
    (e : {rs : ι × ι // P rs.1 rs.2} → k) (a : {rs : ι × ι // P rs.1 rs.2}) :
    (h * ext0 P e) a.1.1 a.1.2 = (lm P h).mulVec e a := by sorry
