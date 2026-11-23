-- Prove2me | Theorems.Thm_GlobalTheory_exists_complete_discreteValuationRing_ker_eq
-- name    : GlobalTheory.exists_complete_discreteValuationRing_ker_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:03.239007+00:00
-- url     : https://prove2.me/theorems/b93c1c93-67a6-4121-a16a-980b470497dc
-- title:
--   Global Theory: exists complete discrete Valuation Ring ker eq
-- statement:
--   The Global Theory construction uses the exists complete discrete Valuation Ring ker eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L642-L654
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L642-L654

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

theorem GlobalTheory.exists_complete_discreteValuationRing_ker_eq {S : Type u} [CommRing S]
    [IsNoetherianRing S] [IsLocalRing S] (q : Ideal S) [q.IsPrime] (hq : q ≠ maximalIdeal S) :
    ∃ (O : Type u) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (maximalIdeal O) O) (φ : S →+* O),
      RingHom.ker φ = q ∧ IsLocalHom φ := by sorry
