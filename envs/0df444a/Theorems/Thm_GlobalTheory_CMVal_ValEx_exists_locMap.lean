-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_ValEx_exists_locMap
-- name    : GlobalTheory.CMVal.ValEx.exists_locMap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:23.190289+00:00
-- url     : https://prove2.me/theorems/db49eddb-3249-4834-9cef-231e7cb12613
-- title:
--   Val Ex: exists loc Map
-- statement:
--   The Val Ex construction uses the exists loc Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L139-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L139-L158

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

theorem GlobalTheory.CMVal.ValEx.exists_locMap (σ : E ≃+* E) (w w' : HeightOneSpectrum (𝓞 E)) (h : ∀ y, w'.valuation E y = w.valuation E (σ y)) :
    ∃ c : w'.adicCompletion E →+* w.adicCompletion E, Continuous c ∧
      (∀ y, c (algebraMap E _ y) = algebraMap E _ (σ y)) ∧ ∀ x, Valued.v (c x) = Valued.v x := by sorry
