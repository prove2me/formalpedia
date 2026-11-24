-- Prove2me | Theorems.Thm_GlobalTheory_FinsetSumSmulCoe_coeFn_finset_sum_smul
-- name    : GlobalTheory.FinsetSumSmulCoe.coeFn_finset_sum_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:01:20.851967+00:00
-- url     : https://prove2.me/theorems/0939d576-8595-4b1b-a799-76a075640454
-- title:
--   Finset Sum Smul Coe: coe Fn finset sum smul
-- statement:
--   The Finset Sum Smul Coe construction uses the coe Fn finset sum smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CoeFnFinsetSumSmul.lean#L5-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CoeFnFinsetSumSmul.lean#L5-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CoeFnFinsetSumSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.FinsetSumSmulCoe

theorem GlobalTheory.FinsetSumSmulCoe.coeFn_finset_sum_smul {α : Type} [MeasurableSpace α] {μ : Measure α} {ι : Type}
    (c : ι → ℂ) (u : ι → Lp ℂ (2 : ENNReal) μ) (s : Finset ι) :
    (((∑ i ∈ s, c i • u i : Lp ℂ (2 : ENNReal) μ) : α →ₘ[μ] ℂ) : α → ℂ) =ᵐ[μ]
      fun x => ∑ i ∈ s, c i * (((u i : α →ₘ[μ] ℂ)) : α → ℂ) x := by sorry
