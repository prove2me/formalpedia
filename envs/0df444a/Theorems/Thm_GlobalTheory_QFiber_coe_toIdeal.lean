-- Prove2me | Theorems.Thm_GlobalTheory_QFiber_coe_toIdeal
-- name    : GlobalTheory.QFiber.coe_toIdeal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:02:30.661806+00:00
-- url     : https://prove2.me/theorems/010280ec-7bca-41a5-9aa5-c91d07fd13d6
-- title:
--   QFiber: coe to Ideal
-- statement:
--   The QFiber construction uses the coe to Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardHilbertEisensteinFourierFiberLeNorm.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardHilbertEisensteinFourierFiberLeNorm.lean#L19-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDivisorsLeAbsNormNumberFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardHilbertEisensteinFourierFiberLeNorm
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
noncomputable section
open GlobalTheory GlobalTheory.QFiber
open FractionalIdeal
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.QFiber.coe_toIdeal {K : FractionalIdeal (𝓞 F)⁰ F} (h : K ≤ 1) :
    ((toIdeal K : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = K := by sorry
