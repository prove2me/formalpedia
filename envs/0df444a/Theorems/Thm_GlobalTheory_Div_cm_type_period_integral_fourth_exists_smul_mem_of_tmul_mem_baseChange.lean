-- Prove2me | Theorems.Thm_GlobalTheory_Div_cm_type_period_integral_fourth_exists_smul_mem_of_tmul_mem_baseChange
-- name    : GlobalTheory.Div.cm_type_period_integral_fourth.exists_smul_mem_of_tmul_mem_baseChange
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:50:27.319377+00:00
-- url     : https://prove2.me/theorems/64ae07c7-ae78-40bc-8e43-d7e94801ac02
-- title:
--   cm type period integral fourth: exists smul mem of tmul mem base Change
-- statement:
--   The cm type period integral fourth construction uses the exists smul mem of tmul mem base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralFourth.lean#L8-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralFourth.lean#L8-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralFourth
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
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.cm_type_period_integral_fourth

theorem GlobalTheory.Div.cm_type_period_integral_fourth.exists_smul_mem_of_tmul_mem_baseChange {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K]
    [IsFractionRing O K] {H : Type} [AddCommGroup H] [Module O H] (Fil : Submodule O H) (h : H)
    (hh : (1 : K) ⊗ₜ[O] h ∈ Fil.baseChange K) : ∃ d : O, d ≠ 0 ∧ d • h ∈ Fil := by sorry
