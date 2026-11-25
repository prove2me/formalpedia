-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Model_IsValChar_expIn_eq
-- name    : GlobalTheory.CMVal.Model.IsValChar.expIn_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:58:52.703115+00:00
-- url     : https://prove2.me/theorems/c70f1e84-6671-404f-abae-90717bdf4656
-- title:
--   Is Val Char: exp In eq
-- statement:
--   The Is Val Char construction uses the exp In eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L202-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L202-L206

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

theorem GlobalTheory.CMVal.Model.IsValChar.expIn_eq {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 𝔤 : Ideal (OF E)}
    {χ : HChar E} (h : IsValChar φ s κ 𝔣 ∅ χ) (h' : IsValChar φ s κ 𝔤 ∅ χ) (v : HeightOneSpectrum (OF E)) :
    expIn 𝔣 v = expIn 𝔤 v := by sorry
