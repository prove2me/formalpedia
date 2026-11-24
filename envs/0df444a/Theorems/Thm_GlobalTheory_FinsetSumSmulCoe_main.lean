-- Prove2me | Theorems.Thm_GlobalTheory_FinsetSumSmulCoe_main
-- name    : GlobalTheory.FinsetSumSmulCoe.main
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:12:37.300911+00:00
-- url     : https://prove2.me/theorems/a7206cda-3fa5-489f-a870-5a62c397735d
-- title:
--   Finset Sum Smul Coe: main
-- statement:
--   The Finset Sum Smul Coe construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CoeFnFinsetSumSmul.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CoeFnFinsetSumSmul.lean#L22-L24

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

theorem GlobalTheory.FinsetSumSmulCoe.main : ∀ {α : Type} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {ι : Type} [inst_1 : Fintype ι] (c : ι → ℂ) (u : ι → ↥(MeasureTheory.Lp ℂ (2 : ENNReal) μ)), (↑(↑(∑ i : ι, c i • u i) : α →ₘ[μ] ℂ) : α → ℂ) =ᵐ[μ] fun (x : α) ↦ ∑ i : ι, c i * (↑(↑(u i) : α →ₘ[μ] ℂ) : α → ℂ) x := by sorry
