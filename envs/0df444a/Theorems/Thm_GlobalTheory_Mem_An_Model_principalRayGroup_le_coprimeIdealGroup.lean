-- Prove2me | Theorems.Thm_GlobalTheory_Mem_An_Model_principalRayGroup_le_coprimeIdealGroup
-- name    : GlobalTheory.Mem.An.Model.principalRayGroup_le_coprimeIdealGroup
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:06.441229+00:00
-- url     : https://prove2.me/theorems/9ace399f-d305-4d19-86da-8547b2443af3
-- title:
--   Model: principal Ray Group le coprime Ideal Group
-- statement:
--   The Model construction uses the principal Ray Group le coprime Ideal Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NormOneSevenOneTwo.lean#L74-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NormOneSevenOneTwo.lean#L74-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NormOneSevenOneTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An GlobalTheory.Mem.An.Model

theorem GlobalTheory.Mem.An.Model.principalRayGroup_le_coprimeIdealGroup {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) : rayP 𝔮 ≤ rayI 𝔮 := by sorry
