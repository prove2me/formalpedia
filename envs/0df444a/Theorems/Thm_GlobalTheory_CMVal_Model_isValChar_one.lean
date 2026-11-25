-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Model_isValChar_one
-- name    : GlobalTheory.CMVal.Model.isValChar_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:59.917805+00:00
-- url     : https://prove2.me/theorems/f052e051-31e1-4e36-b8e6-37b91247eba4
-- title:
--   Model: is Val Char one
-- statement:
--   The Model construction uses the is Val Char one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L57-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L57-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Model
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.Model.isValChar_one {I : Type} [Fintype I] (φ : I → E →+* ℂ) (Q : Finset (HeightOneSpectrum (OF E))) :
    IsValChar φ 0 (fun _ => 0) ⊤ Q (1 : HChar E) := by sorry
