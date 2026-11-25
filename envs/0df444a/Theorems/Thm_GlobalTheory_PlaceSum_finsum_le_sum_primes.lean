-- Prove2me | Theorems.Thm_GlobalTheory_PlaceSum_finsum_le_sum_primes
-- name    : GlobalTheory.PlaceSum.finsum_le_sum_primes
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:49:57.417638+00:00
-- url     : https://prove2.me/theorems/81754cf8-c6eb-4725-a40c-9bc5d6696f8e
-- title:
--   Place Sum: finsum le sum primes
-- statement:
--   The Place Sum construction uses the finsum le sum primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumFinitePlacesLeSumOverPrimes.lean#L71-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumFinitePlacesLeSumOverPrimes.lean#L71-L113

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumFinitePlacesLeSumOverPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Pj
open GlobalTheory GlobalTheory.PlaceSum
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.PlaceSum.finsum_le_sum_primes (K : Type) [Field K] [NumberField K] (φ : ℕ → ℝ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hφ : ∀ p, 0 ≤ φ p) (ν : HeightOneSpectrum (𝓞 K) → ℝ) (h0 : ∀ la, 0 ≤ ν la)
    (hle : ∀ la, ν la ≤ (ramOverZ la : ℝ) * φ (resCharOf la)) (hz : ∀ la, resCharOf la ∉ S → ν la = 0) :
    (Function.support ν).Finite ∧
      (∑ᶠ la, |ν la| * (Real.log (Ideal.absNorm la.asIdeal) / Module.finrank ℚ K)) ≤
        ∑ p ∈ S, φ p * Real.log p := by sorry
