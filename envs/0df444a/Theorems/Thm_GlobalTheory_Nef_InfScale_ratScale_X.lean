-- Prove2me | Theorems.Thm_GlobalTheory_Nef_InfScale_ratScale_X
-- name    : GlobalTheory.Nef.InfScale.ratScale_X
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:00:20.243543+00:00
-- url     : https://prove2.me/theorems/7c1a7bf2-fb67-4178-a7e9-a437b091508b
-- title:
--   Inf Scale: rat Scale X
-- statement:
--   The Inf Scale construction uses the rat Scale X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsScalingCompatibleExpansionAtInfinity.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsScalingCompatibleExpansionAtInfinity.lean#L87-L89

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

theorem GlobalTheory.Nef.InfScale.ratScale_X (c : F) (hc : c ≠ 0) :
    ratScale c hc RatFunc.X = RatFunc.C c * RatFunc.X := by sorry
