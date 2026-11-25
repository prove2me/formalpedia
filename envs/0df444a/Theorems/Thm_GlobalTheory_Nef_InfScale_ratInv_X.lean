-- Prove2me | Theorems.Thm_GlobalTheory_Nef_InfScale_ratInv_X
-- name    : GlobalTheory.Nef.InfScale.ratInv_X
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:01:44.881098+00:00
-- url     : https://prove2.me/theorems/aac615f9-be97-4a82-b39a-b813b1f679a1
-- title:
--   Inf Scale: rat Inv X
-- statement:
--   The Inf Scale construction uses the rat Inv X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsScalingCompatibleExpansionAtInfinity.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsScalingCompatibleExpansionAtInfinity.lean#L94-L95

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

theorem GlobalTheory.Nef.InfScale.ratInv_X : ratInv (RatFunc.X : RatFunc F) = RatFunc.X⁻¹ := by sorry
