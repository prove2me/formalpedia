-- Prove2me | Theorems.Thm_GlobalTheory_LocBounded_bounded_of_isIntegral
-- name    : GlobalTheory.LocBounded.bounded_of_isIntegral
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:12:51.633562+00:00
-- url     : https://prove2.me/theorems/1e29a06b-9b53-43ed-b565-c78adc3a1b77
-- title:
--   Loc Bounded: bounded of is Integral
-- statement:
--   The Loc Bounded construction uses the bounded of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedOfIsIntegral.lean#L198-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedOfIsIntegral.lean#L198-L205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
noncomputable section
open GlobalTheory GlobalTheory.LocBounded

theorem GlobalTheory.LocBounded.bounded_of_isIntegral : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (N : Matrix (Fin n) (Fin n) (w.adicCompletion E)), N.charpoly.Separable → ∃ c : WithZero (Multiplicative ℤ), ∀ g ∈ Algebra.adjoin (w.adicCompletion E) {N}, IsIntegral (w.adicCompletionIntegers E) g → ∀ i j, Valued.v (g i j) ≤ c := by sorry
