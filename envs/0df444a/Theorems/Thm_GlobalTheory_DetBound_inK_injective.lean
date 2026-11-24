-- Prove2me | Theorems.Thm_GlobalTheory_DetBound_inK_injective
-- name    : GlobalTheory.DetBound.inK_injective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:59:30.341388+00:00
-- url     : https://prove2.me/theorems/c3628473-37d3-4ff4-a621-08fb52c4aa2c
-- title:
--   Det Bound: in K injective
-- statement:
--   The Det Bound construction uses the in K injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodTraceIntegral.lean#L107-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodTraceIntegral.lean#L107-L113

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

theorem GlobalTheory.DetBound.inK_injective {O : Type} [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (H : Type) [AddCommGroup H] [Module O H] [Module.Free O H] : Function.Injective (inK K H (O := O)) := by sorry
