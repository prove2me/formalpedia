-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_HatCap_isOpen_integral
-- name    : GlobalTheory.CMVal.HatCap.isOpen_integral
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:05:18.751386+00:00
-- url     : https://prove2.me/theorems/b60dfdf0-e336-417c-9e11-09d2d547be54
-- title:
--   Hat Cap: is Open integral
-- statement:
--   The Hat Cap construction uses the is Open integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdelicRingClassLatticeOneEqOrder.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdelicRingClassLatticeOneEqOrder.lean#L13-L18

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdelicRingClassLatticeOneEqOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.HatCap
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.HatCap.isOpen_integral :
    IsOpen {y : Af E | ∀ v : HeightOneSpectrum (𝓞 E), y v ∈ v.adicCompletionIntegers E} := by sorry
