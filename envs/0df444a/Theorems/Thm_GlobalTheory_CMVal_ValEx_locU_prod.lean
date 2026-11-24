-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_ValEx_locU_prod
-- name    : GlobalTheory.CMVal.ValEx.locU_prod
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:07:10.17328+00:00
-- url     : https://prove2.me/theorems/f20ea612-9106-44c2-8e3d-bd317800078b
-- title:
--   Val Ex: loc U prod
-- statement:
--   The Val Ex construction uses the loc U prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L423-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L423-L428

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
open Classical

theorem GlobalTheory.CMVal.ValEx.locU_prod (S : Finset (HeightOneSpectrum (𝓞 E))) (k : Eˣ) (Q : HeightOneSpectrum (𝓞 E)) :
    locU Q (∏ P ∈ S, single P (toLoc P k)) = if Q ∈ S then toLoc Q k else 1 := by sorry
