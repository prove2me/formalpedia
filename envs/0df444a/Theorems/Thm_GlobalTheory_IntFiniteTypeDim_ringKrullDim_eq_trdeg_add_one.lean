-- Prove2me | Theorems.Thm_GlobalTheory_IntFiniteTypeDim_ringKrullDim_eq_trdeg_add_one
-- name    : GlobalTheory.IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:05:18.850803+00:00
-- url     : https://prove2.me/theorems/f9d15f58-ce97-4394-999e-08525b193438
-- title:
--   Int Finite Type Dim: ring Krull Dim eq trdeg add one
-- statement:
--   The Int Finite Type Dim construction uses the ring Krull Dim eq trdeg add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingKrullDimQuotientLeOfMinimalPrimes.lean#L38-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingKrullDimQuotientLeOfMinimalPrimes.lean#L38-L70

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

theorem GlobalTheory.IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one :
    ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A],
      Function.Injective (algebraMap ℤ A) →
        ringKrullDim A = ((Cardinal.toENat (Algebra.trdeg ℤ A) + 1 : ℕ∞) : WithBot ℕ∞) := by sorry
