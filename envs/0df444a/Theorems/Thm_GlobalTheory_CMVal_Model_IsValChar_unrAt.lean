-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Model_IsValChar_unrAt
-- name    : GlobalTheory.CMVal.Model.IsValChar.unrAt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:29.695829+00:00
-- url     : https://prove2.me/theorems/de801d44-ef35-451b-a9d2-9d159ae72a0c
-- title:
--   Is Val Char: unr At
-- statement:
--   The Is Val Char construction uses the unr At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L181-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L181-L186

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

theorem GlobalTheory.CMVal.Model.IsValChar.unrAt {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)}
    {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E} (h : IsValChar φ s κ 𝔣 Q χ)
    {v : HeightOneSpectrum (OF E)} {P : HeightOneSpectrum (𝓞 E)} (hP : Over P v) (hQ : v ∉ Q) (hf : ¬ v.asIdeal ∣ 𝔣) :
    UnrAt χ P := by sorry
