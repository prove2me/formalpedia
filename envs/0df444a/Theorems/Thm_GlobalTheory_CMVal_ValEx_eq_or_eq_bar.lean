-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_ValEx_eq_or_eq_bar
-- name    : GlobalTheory.CMVal.ValEx.eq_or_eq_bar
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:07:20.247009+00:00
-- url     : https://prove2.me/theorems/3b28fcbf-379f-4ec1-9530-1c94e7ff0e88
-- title:
--   Val Ex: eq or eq bar
-- statement:
--   The Val Ex construction uses the eq or eq bar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L332-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L332-L350

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

theorem GlobalTheory.CMVal.ValEx.eq_or_eq_bar {w P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (OF E)} (h : Over w v) (hP : Over P v) :
    P = w ∨ P = bar w := by sorry
