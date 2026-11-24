-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_ValEx_isOpen_cong
-- name    : GlobalTheory.CMVal.ValEx.isOpen_cong
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:42.386236+00:00
-- url     : https://prove2.me/theorems/63fbaece-fa8e-42ee-bda7-e8ff571d9b41
-- title:
--   Val Ex: is Open cong
-- statement:
--   The Val Ex construction uses the is Open cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L161-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L161-L167

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
open WithZeroTopology

theorem GlobalTheory.CMVal.ValEx.isOpen_cong (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    IsOpen (cong (Valued.v : Valuation (w.adicCompletion E) ℤᵐ⁰) n : Set (w.adicCompletion E)ˣ) := by sorry
