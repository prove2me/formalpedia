-- Prove2me | Theorems.Thm_GlobalTheory_Nef_InfScale_lsScale_rat
-- name    : GlobalTheory.Nef.InfScale.lsScale_rat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:02:55.188504+00:00
-- url     : https://prove2.me/theorems/fe2efba9-a410-4c90-8b0e-a77e359b09e7
-- title:
--   Inf Scale: ls Scale rat
-- statement:
--   The Inf Scale construction uses the ls Scale rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsScalingCompatibleExpansionAtInfinity.lean#L118-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsScalingCompatibleExpansionAtInfinity.lean#L118-L128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsScalingCompatibleExpansionAtInfinity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.InfScale
variable {F : Type} [Field F]

theorem GlobalTheory.Nef.InfScale.lsScale_rat (c : F) (hc : c ≠ 0) :
    (lsScale c hc).comp (algebraMap (RatFunc F) (LaurentSeries F)) =
      (algebraMap (RatFunc F) (LaurentSeries F)).comp (ratScale c hc) := by sorry
