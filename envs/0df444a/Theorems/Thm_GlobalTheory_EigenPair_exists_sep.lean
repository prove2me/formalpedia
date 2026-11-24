-- Prove2me | Theorems.Thm_GlobalTheory_EigenPair_exists_sep
-- name    : GlobalTheory.EigenPair.exists_sep
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:56:44.445+00:00
-- url     : https://prove2.me/theorems/f722a28e-2281-4efb-9e3a-d36cb2ed2034
-- title:
--   Eigen Pair: exists sep
-- statement:
--   The Eigen Pair construction uses the exists sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralFifth.lean#L18-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralFifth.lean#L18-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralFifth
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
open GlobalTheory GlobalTheory.EigenPair
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.EigenPair.exists_sep {K : Type} [Field K] [CharZero K] (c : Ideal (OF E)) (hc : c ≠ ⊥) (σ σ' : E →+* K)
    (h : σ' ≠ bar σ) : ∃ a b : orderC c, (b : E) = IsCMField.complexConj E a ∧ σ a ≠ σ' b := by sorry
