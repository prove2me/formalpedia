-- Prove2me | Theorems.Thm_GlobalTheory_LipschitzTR_LhsSum_one_le_abs_prod_int
-- name    : GlobalTheory.LipschitzTR.LhsSum.one_le_abs_prod_int
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:11:24.829792+00:00
-- url     : https://prove2.me/theorems/4ecb3aa4-342f-46d1-9992-e380f08b0a97
-- title:
--   Lhs Sum: one le abs prod int
-- statement:
--   The Lhs Sum construction uses the one le abs prod int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableLipschitzLatticeNormPowSummand.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableLipschitzLatticeNormPowSummand.lean#L28-L35

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzTR GlobalTheory.LipschitzTR.LhsSum
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.LipschitzTR.LhsSum.one_le_abs_prod_int [IsTotallyReal F] (y : 𝓞 F) (hy : y ≠ 0) :
    1 ≤ |∏ τ : F →+* ℝ, τ (y : F)| := by sorry
