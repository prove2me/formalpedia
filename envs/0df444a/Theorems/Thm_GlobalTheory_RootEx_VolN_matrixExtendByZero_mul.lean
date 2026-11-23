-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_VolN_matrixExtendByZero_mul
-- name    : GlobalTheory.RootEx.VolN.matrixExtendByZero_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:31.641804+00:00
-- url     : https://prove2.me/theorems/f66de0a0-2a6e-4000-9b8d-dea77eca5054
-- title:
--   Vol N: matrix Extend By Zero mul
-- statement:
--   The Vol N construction uses the matrix Extend By Zero mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L47-L53

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

theorem GlobalTheory.RootEx.VolN.matrixExtendByZero_mul (P : ι → ι → Prop) [DecidableRel P] [F : Fintype {rs : ι × ι // P rs.1 rs.2}] (h : Matrix ι ι k)
    (e : {rs : ι × ι // P rs.1 rs.2} → k) (a : {rs : ι × ι // P rs.1 rs.2}) :
    (ext0 P e * h) a.1.1 a.1.2 = (rm P h).mulVec e a := by sorry
