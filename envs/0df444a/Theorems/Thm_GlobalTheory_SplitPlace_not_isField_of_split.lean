-- Prove2me | Theorems.Thm_GlobalTheory_SplitPlace_not_isField_of_split
-- name    : GlobalTheory.SplitPlace.not_isField_of_split
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:26:04.884456+00:00
-- url     : https://prove2.me/theorems/ad81ec60-7853-4582-8632-9373143374c4
-- title:
--   Split Place: not is Field of split
-- statement:
--   The Split Place construction uses the not is Field of split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NotIsFieldAdicCompletionTensorOfSplit.lean#L55-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NotIsFieldAdicCompletionTensorOfSplit.lean#L55-L163

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NotIsFieldAdicCompletionTensorOfSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain Polynomial
open GlobalTheory GlobalTheory.SplitPlace
open scoped TensorProduct
open NumberField IsDedekindDomain Polynomial

theorem GlobalTheory.SplitPlace.not_isField_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E], Module.finrank F E = 2 → ∀ v : HeightOneSpectrum (𝓞 F),
    (v.asIdeal.primesOver (𝓞 E)).ncard = 2 → ¬ IsField (v.adicCompletion F ⊗[F] E) := by sorry
