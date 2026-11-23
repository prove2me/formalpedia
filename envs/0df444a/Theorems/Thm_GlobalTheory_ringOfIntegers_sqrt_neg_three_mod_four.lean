-- Prove2me | Theorems.Thm_GlobalTheory_ringOfIntegers_sqrt_neg_three_mod_four
-- name    : GlobalTheory.ringOfIntegers_sqrt_neg_three_mod_four
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:22.355076+00:00
-- url     : https://prove2.me/theorems/628f5856-5009-45ae-ae36-2704fa596629
-- title:
--   Global Theory: ring Of Integers sqrt neg three mod four
-- statement:
--   The Global Theory construction uses the ring Of Integers sqrt neg three mod four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/RingOfIntegersSqrtNegThreeModFour.lean#L166-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/RingOfIntegersSqrtNegThreeModFour.lean#L166-L210

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RingOfIntegersSqrtNegThreeModFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open GlobalTheory
open QuadraticZeta

theorem GlobalTheory.ringOfIntegers_sqrt_neg_three_mod_four (d : ℕ) (hsq : Squarefree d) (hd : d % 4 = 3)
    (K : Type) [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2) (r : K)
    (hr : r ^ 2 = -(d : K)) :
    ∃ (w : 𝓞 K) (bar : 𝓞 K →+* 𝓞 K), 2 * (w : K) = 1 + r ∧ w + bar w = 1 ∧
      (∀ c : 𝓞 K, ∃ m n : ℤ, c = m + n * w) ∧
      (∀ σ : K →+* ℂ, ¬ ComplexEmbedding.IsReal σ ∧
        ∀ c : 𝓞 K, σ (bar c : K) = starRingEnd ℂ (σ (c : K))) ∧
      ∃ σ : K →+* ℂ, σ r = Complex.I * √d := by sorry
