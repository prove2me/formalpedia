-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_ValEx_isOfFinOrder_div
-- name    : GlobalTheory.CMVal.ValEx.isOfFinOrder_div
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:32.290864+00:00
-- url     : https://prove2.me/theorems/6e53ae2e-3240-41b6-951a-472c7fde8558
-- title:
--   Val Ex: is Of Fin Order div
-- statement:
--   The Val Ex construction uses the is Of Fin Order div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L352-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L352-L362

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
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
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
local notation "cc" => IsCMField.complexConj E

theorem GlobalTheory.CMVal.ValEx.isOfFinOrder_div (k : Eˣ) (h : ∀ w : HeightOneSpectrum (𝓞 E), (bar w).valuation E k = w.valuation E k) :
    IsOfFinOrder (k / Units.map (cc).toRingEquiv.toMonoidHom k) := by sorry
