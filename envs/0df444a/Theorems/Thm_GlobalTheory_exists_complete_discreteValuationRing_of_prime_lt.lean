-- Prove2me | Theorems.Thm_GlobalTheory_exists_complete_discreteValuationRing_of_prime_lt
-- name    : GlobalTheory.exists_complete_discreteValuationRing_of_prime_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:32.956387+00:00
-- url     : https://prove2.me/theorems/2b19ce37-aecd-40a5-9ca7-256698f01e72
-- title:
--   Global Theory: exists complete discrete Valuation Ring of prime lt
-- statement:
--   The Global Theory construction uses the exists complete discrete Valuation Ring of prime lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L656-L676
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L656-L676

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u v w
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

theorem GlobalTheory.exists_complete_discreteValuationRing_of_prime_lt {A : Type u} [CommRing A]
    [IsNoetherianRing A] (q p : Ideal A) [q.IsPrime] [p.IsPrime] (hqp : q < p) :
    ∃ (O : Type u) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (maximalIdeal O) O) (φ : A →+* O),
      RingHom.ker φ = q ∧ (maximalIdeal O).comap φ = p := by sorry
