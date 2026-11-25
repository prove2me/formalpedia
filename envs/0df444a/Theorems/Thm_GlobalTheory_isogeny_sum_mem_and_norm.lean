-- Prove2me | Theorems.Thm_GlobalTheory_isogeny_sum_mem_and_norm
-- name    : GlobalTheory.isogeny_sum_mem_and_norm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:09:07.867388+00:00
-- url     : https://prove2.me/theorems/9df3b1e7-1e6c-474b-8d59-655457a9a715
-- title:
--   Global Theory: isogeny sum mem and norm
-- statement:
--   The Global Theory construction uses the isogeny sum mem and norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ContinuousThetaSectionPointwiseNormSq.lean#L226-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ContinuousThetaSectionPointwiseNormSq.lean#L226-L311

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ContinuousThetaSectionPointwiseNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Complex ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory
open IsogenySum FockTranslation

theorem GlobalTheory.isogeny_sum_mem_and_norm {ι : Type} [Fintype ι] (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
    (hU : ∀ (q : ℕ) a F v, U q a F v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
    (Y Y' : GT ι) (hY : (∀ x ∈ lat Y.b, ∀ y ∈ lat Y.b, Y.ka (x + y) = Y.ka x * Y.ka y * cexp (Real.pi * I * (Hf x y).im))) (hY' : (∀ x ∈ lat Y'.b, ∀ y ∈ lat Y'.b, Y'.ka (x + y) = Y'.ka x * Y'.ka y * cexp (Real.pi * I * (Hf x y).im)))
    (hag : ∀ x ∈ lat Y.b, x ∈ lat Y'.b → Y.ka x = Y'.ka x)
    (R : Finset (EuclideanSpace ℂ ι)) (hR : ∀ y ∈ R, y ∈ lat Y'.b) (hR' : ∀ y ∈ lat Y'.b, ∃! r ∈ R, y - r ∈ lat Y.b)
    (F : EuclideanSpace ℂ ι → ℂ) (hF : F ∈ Y.Sec 1) :
    (∑ y ∈ R, Y'.ka y • U 1 y F) ∈ Y'.Sec 1 ∧ Y'.l2 1 (∑ y ∈ R, Y'.ka y • U 1 y F) = R.card * Y.l2 1 F := by sorry
