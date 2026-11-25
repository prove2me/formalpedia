-- Prove2me | Theorems.Thm_GlobalTheory_IntFiniteTypeDim_ringKrullDim_quotient_le_of_minimalPrimes
-- name    : GlobalTheory.IntFiniteTypeDim.ringKrullDim_quotient_le_of_minimalPrimes
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:15:30.18635+00:00
-- url     : https://prove2.me/theorems/cdbebe83-e047-4ef1-baf0-b6e7147f3807
-- title:
--   Int Finite Type Dim: ring Krull Dim quotient le of minimal Primes
-- statement:
--   The Int Finite Type Dim construction uses the ring Krull Dim quotient le of minimal Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingKrullDimQuotientLeOfMinimalPrimes.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingKrullDimQuotientLeOfMinimalPrimes.lean#L25-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrullDimQuotientMinimalPrimeOverL
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingKrullDimQuotientLeOfMinimalPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntFiniteTypeDim

theorem GlobalTheory.IntFiniteTypeDim.ringKrullDim_quotient_le_of_minimalPrimes {A : Type} [CommRing A] (I : Ideal A)
    (c : WithBot ℕ∞) (h : ∀ P ∈ I.minimalPrimes, ringKrullDim (A ⧸ P) ≤ c) :
    ringKrullDim (A ⧸ I) ≤ c := by sorry
