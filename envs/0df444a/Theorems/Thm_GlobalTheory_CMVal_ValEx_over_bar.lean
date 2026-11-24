-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_ValEx_over_bar
-- name    : GlobalTheory.CMVal.ValEx.over_bar
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:54.224986+00:00
-- url     : https://prove2.me/theorems/aef6dbd5-65fc-431c-aad8-76747ef8d2a1
-- title:
--   Val Ex: over bar
-- statement:
--   The Val Ex construction uses the over bar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L322-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L322-L330

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

theorem GlobalTheory.CMVal.ValEx.over_bar {w : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (OF E)} (h : Over w v) : Over (bar w) v := by sorry
