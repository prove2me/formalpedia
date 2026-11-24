-- Prove2me | Theorems.Thm_GlobalTheory_T_abs_norm_le_abs_norm_mul_div_absNorm_of_eisensteinIndexPair
-- name    : GlobalTheory.T.abs_norm_le_abs_norm_mul_div_absNorm_of_eisensteinIndexPair
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:26:54.326653+00:00
-- url     : https://prove2.me/theorems/d471ea89-b05e-4d03-b1ea-68d03d090c9d
-- title:
--   T: abs norm le abs norm mul div abs Norm of eisenstein Index Pair
-- statement:
--   The T construction uses the abs norm le abs norm mul div abs Norm of eisenstein Index Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsNormLeAbsNormMulDivAbsNormOfEisensteinIndexPaStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsNormLeAbsNormMulDivAbsNormOfEisensteinIndexPaStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormLeAbsNormMulDivAbsNormOfEisensteinIndexPa
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormLeAbsNormMulDivAbsNormOfEisensteinIndexPaStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.abs_norm_le_abs_norm_mul_div_absNorm_of_eisensteinIndexPair : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (p : QPair 𝔞 𝔟), |(Algebra.norm ℚ p.1.1 : ℝ)| ≤ |(Algebra.norm ℚ (p.1.1 * p.1.2) : ℝ)| / nrm 𝔟 := by sorry
