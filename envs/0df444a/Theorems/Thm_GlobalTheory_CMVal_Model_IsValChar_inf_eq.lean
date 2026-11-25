-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Model_IsValChar_inf_eq
-- name    : GlobalTheory.CMVal.Model.IsValChar.inf_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:18.307649+00:00
-- url     : https://prove2.me/theorems/d67f1dc1-b762-5494-865c-d209d73d8087
-- title:
--   Is Val Char: inf eq
-- statement:
--   The Is Val Char construction uses the inf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L208-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L208-L212

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

theorem GlobalTheory.CMVal.Model.IsValChar.inf_eq {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)}
    {Q Q' : Finset (HeightOneSpectrum (OF E))} {χ χ' : HChar E} (h : IsValChar φ s κ 𝔣 Q χ) (h' : IsValChar φ s κ 𝔣 Q' χ')
    (k : Eˣ) : (χ * χ'⁻¹).inf k = 1 := by sorry
