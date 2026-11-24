-- Prove2me | Theorems.Thm_GlobalTheory_CMExtend_ringHom_ext_orderC
-- name    : GlobalTheory.CMExtend.ringHom_ext_orderC
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:02:47.729019+00:00
-- url     : https://prove2.me/theorems/1b18d998-a883-4892-a49a-c86b593b6ae3
-- title:
--   CMExtend: ring Hom ext order C
-- statement:
--   The CMExtend construction uses the ring Hom ext order C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodNormIntegral.lean#L131-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodNormIntegral.lean#L131-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodNormIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.CMExtend
variable {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)}
variable {K A : Type} [Field K] [CharZero K] [Ring A] [Algebra K A]

theorem GlobalTheory.CMExtend.ringHom_ext_orderC (hc : c ≠ ⊥) {B : Type} [Ring B] (f₁ f₂ : E →+* B) (h : ∀ a : orderC c, f₁ a = f₂ a) :
    f₁ = f₂ := by sorry
