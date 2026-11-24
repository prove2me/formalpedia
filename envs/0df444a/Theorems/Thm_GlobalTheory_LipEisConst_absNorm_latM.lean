-- Prove2me | Theorems.Thm_GlobalTheory_LipEisConst_absNorm_latM
-- name    : GlobalTheory.LipEisConst.absNorm_latM
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:11:00.077235+00:00
-- url     : https://prove2.me/theorems/853d0ecf-bab5-47f3-8628-2cab4a077af8
-- title:
--   Lip Eis Const: abs Norm lat M
-- statement:
--   The Lip Eis Const construction uses the abs Norm lat M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LipschitzConstantInverseDifferentEisenstein.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LipschitzConstantInverseDifferentEisenstein.lean#L12-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LipschitzConstantInverseDifferentEisenstein
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.LipEisConst
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent

theorem GlobalTheory.LipEisConst.absNorm_latM {F : Type} [Field F] [NumberField F] (𝔞 : Frac F) :
    ((FractionalIdeal.absNorm (latM 𝔞) : ℚ) : ℝ) = (dF F * nrm 𝔞)⁻¹ := by sorry
