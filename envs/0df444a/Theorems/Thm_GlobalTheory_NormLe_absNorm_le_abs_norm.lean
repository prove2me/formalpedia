-- Prove2me | Theorems.Thm_GlobalTheory_NormLe_absNorm_le_abs_norm
-- name    : GlobalTheory.NormLe.absNorm_le_abs_norm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:36:41.926232+00:00
-- url     : https://prove2.me/theorems/17f0e917-209d-4ed3-8687-7b6dec4c31a2
-- title:
--   Norm Le: abs Norm le abs norm
-- statement:
--   The Norm Le construction uses the abs Norm le abs norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsNormLeAbsNormMulDivAbsNormOfEisensteinIndexPa.lean#L9-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsNormLeAbsNormMulDivAbsNormOfEisensteinIndexPa.lean#L9-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormLeAbsNormMulDivAbsNormOfEisensteinIndexPa
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
open GlobalTheory GlobalTheory.NormLe

theorem GlobalTheory.NormLe.absNorm_le_abs_norm {F : Type} [Field F] [NumberField F] (𝔟 : Frac F) {b : F}
    (hb : b ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) (hb0 : b ≠ 0) :
    FractionalIdeal.absNorm (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≤ |Algebra.norm ℚ b| := by sorry
