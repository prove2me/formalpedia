-- Prove2me | Theorems.Thm_GlobalTheory_IntFiniteTypeDim_exists_natPrime_mem_of_isMaximal
-- name    : GlobalTheory.IntFiniteTypeDim.exists_natPrime_mem_of_isMaximal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:15:11.701317+00:00
-- url     : https://prove2.me/theorems/cb10af2f-3e81-44d7-961b-48c2a1212414
-- title:
--   Int Finite Type Dim: exists nat Prime mem of is Maximal
-- statement:
--   The Int Finite Type Dim construction uses the exists nat Prime mem of is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingKrullDimQuotientLeOfMinimalPrimes.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingKrullDimQuotientLeOfMinimalPrimes.lean#L7-L23

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

theorem GlobalTheory.IntFiniteTypeDim.exists_natPrime_mem_of_isMaximal (A : Type) [CommRing A] [Algebra.FiniteType ℤ A]
    (m : Ideal A) [m.IsMaximal] : ∃ l : ℕ, l.Prime ∧ (l : A) ∈ m := by sorry
