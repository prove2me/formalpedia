-- Prove2me | Theorems.Thm_GlobalTheory_EigenPair_natMul_mem_orderC
-- name    : GlobalTheory.EigenPair.natMul_mem_orderC
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:56:42.854419+00:00
-- url     : https://prove2.me/theorems/262ec11e-70be-4290-ab73-ac9cd394f194
-- title:
--   Eigen Pair: nat Mul mem order C
-- statement:
--   The Eigen Pair construction uses the nat Mul mem order C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralFifth.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralFifth.lean#L10-L16

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

theorem GlobalTheory.EigenPair.natMul_mem_orderC (c : Ideal (OF E)) (z : 𝓞 E) :
    ((Ideal.absNorm c : ℕ) : E) * (z : E) ∈ orderC c := by sorry
