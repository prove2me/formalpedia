-- Prove2me | Theorems.Thm_GlobalTheory_Square_sum_le_sum_add_card_mul
-- name    : GlobalTheory.Square.sum_le_sum_add_card_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:19:21.301575+00:00
-- url     : https://prove2.me/theorems/a68f8b1e-622f-4885-89eb-3331e5a31e12
-- title:
--   Square: sum le sum add card mul
-- statement:
--   The Square construction uses the sum le sum add card mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumCompLeSumOfInjOn.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumCompLeSumOfInjOn.lean#L20-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumCompLeSumOfInjOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
open GlobalTheory GlobalTheory.Square

theorem GlobalTheory.Square.sum_le_sum_add_card_mul {ι : Type*} (T : Finset ι) (S : Finset ℤ) (f : ι → ℤ)
    (g : ℤ → ℝ) (u : ι → ℝ) (c : ℝ) (hf : Set.InjOn f T) (hS : ∀ t ∈ T, f t ∈ S)
    (hg : ∀ s ∈ S, 0 ≤ g s) (hu : ∀ t ∈ T, u t ≤ g (f t) + c) :
    ∑ t ∈ T, u t ≤ ∑ s ∈ S, g s + (T.card : ℝ) * c := by sorry
