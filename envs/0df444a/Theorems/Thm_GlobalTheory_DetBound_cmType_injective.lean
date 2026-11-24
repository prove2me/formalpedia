-- Prove2me | Theorems.Thm_GlobalTheory_DetBound_cmType_injective
-- name    : GlobalTheory.DetBound.cmType_injective
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:44:03.579675+00:00
-- url     : https://prove2.me/theorems/e0936d68-2260-45f2-894b-80c82a33c2fb
-- title:
--   Det Bound: cm Type injective
-- statement:
--   The Det Bound construction uses the cm Type injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodTraceIntegral.lean#L115-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodTraceIntegral.lean#L115-L119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodTraceIntegral
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
open GlobalTheory GlobalTheory.DetBound
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

theorem GlobalTheory.DetBound.cmType_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type} [Field K] {I : Type}
    {φ : I → E →+* K} (hφ : IsCMTypeIn φ) : Function.Injective φ := by sorry
