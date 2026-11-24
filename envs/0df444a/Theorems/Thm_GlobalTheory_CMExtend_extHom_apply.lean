-- Prove2me | Theorems.Thm_GlobalTheory_CMExtend_extHom_apply
-- name    : GlobalTheory.CMExtend.extHom_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:02:54.354586+00:00
-- url     : https://prove2.me/theorems/77745bda-bba7-4e4a-814a-cd5c998033ed
-- title:
--   CMExtend: ext Hom apply
-- statement:
--   The CMExtend construction uses the ext Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodNormIntegral.lean#L124-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodNormIntegral.lean#L124-L129

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

theorem GlobalTheory.CMExtend.extHom_apply (hc : c ≠ ⊥) (g : orderC c →+* A) (a : orderC c) : extHom K hc g a = g a := by sorry
