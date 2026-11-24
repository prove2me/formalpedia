-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_VolN_det_block_unitri
-- name    : GlobalTheory.RootEx.VolN.det_block_unitri
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:58.708803+00:00
-- url     : https://prove2.me/theorems/946921a7-0fe1-45a2-8f47-e9103bd42731
-- title:
--   Vol N: det block unitri
-- statement:
--   The Vol N construction uses the det block unitri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L108-L112

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

theorem GlobalTheory.RootEx.VolN.det_block_unitri (b : ι → ℕ) (M : Matrix ι ι k)
    (hM : ∀ r s, b s ≤ b r → M r s = (1 : Matrix ι ι k) r s) (Q : ι → Prop) [DecidablePred Q] :
    (M.toSquareBlockProp Q).det = 1 := by sorry
