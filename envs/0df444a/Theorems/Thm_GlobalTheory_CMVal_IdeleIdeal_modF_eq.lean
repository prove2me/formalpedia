-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_IdeleIdeal_modF_eq
-- name    : GlobalTheory.CMVal.IdeleIdeal.modF_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:04:58.917575+00:00
-- url     : https://prove2.me/theorems/a19a987f-1d5b-4741-acab-38812306ecc1
-- title:
--   Idele Ideal: mod F eq
-- statement:
--   The Idele Ideal construction uses the mod F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealSectionIntegralFiniteIdeleUpToUnits.lean#L37-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealSectionIntegralFiniteIdeleUpToUnits.lean#L37-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSectionIntegralFiniteIdeleUpToUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.IdeleIdeal
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.IdeleIdeal.modF_eq {y : (Af E)ˣ} (h : ∀ w, Valued.v ((y : Af E) w) ≤ 1) :
    modF y = ((Ideal.absNorm (idealOf y) : ℕ) : ℝ)⁻¹ := by sorry
