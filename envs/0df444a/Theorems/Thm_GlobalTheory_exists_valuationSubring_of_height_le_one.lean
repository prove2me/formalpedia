-- Prove2me | Theorems.Thm_GlobalTheory_exists_valuationSubring_of_height_le_one
-- name    : GlobalTheory.exists_valuationSubring_of_height_le_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:09.184147+00:00
-- url     : https://prove2.me/theorems/f7ae84aa-2609-490e-a61a-3dd0dfa5fc5f
-- title:
--   Global Theory: exists valuation Subring of height le one
-- statement:
--   The Global Theory construction uses the exists valuation Subring of height le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L106-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L106-L152

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
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
universe u

theorem GlobalTheory.exists_valuationSubring_of_height_le_one {O K : Type*} {B : Type u} [CommRing O]
    [IsDomain O] [IsNoetherianRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B]
    (hinj : Function.Injective (algebraMap O B))
    (m : Ideal B) [hm : m.IsMaximal] (h1 : m.height ≤ 1) (π : O) (hπ : π ≠ 0)
    (hπm : algebraMap O B π ∈ m) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (φ : B →+* O'),
      (∀ a : O, (φ (algebraMap O B a) : K') = algebraMap K K' (algebraMap O K a)) ∧
      Function.Injective φ ∧ (maximalIdeal O').comap φ = m := by sorry
