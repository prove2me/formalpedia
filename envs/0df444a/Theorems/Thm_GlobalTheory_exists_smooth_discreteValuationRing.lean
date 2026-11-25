-- Prove2me | Theorems.Thm_GlobalTheory_exists_smooth_discreteValuationRing
-- name    : GlobalTheory.exists_smooth_discreteValuationRing
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:45:15.145917+00:00
-- url     : https://prove2.me/theorems/8bbe7a18-d5c0-50e2-b3f0-46cf2eaf753e
-- title:
--   Global Theory: exists smooth discrete Valuation Ring
-- statement:
--   The Global Theory construction uses the exists smooth discrete Valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L653-L675
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L653-L675

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
open Polynomial
variable (K : Type*) [Field K]

theorem GlobalTheory.exists_smooth_discreteValuationRing :
    ∃ (V : Subalgebra K (RatFunc K)) (_ : IsDiscreteValuationRing V),
      Algebra.EssFiniteType K V ∧ Algebra.FormallySmooth K V ∧ IsFractionRing V (RatFunc K) ∧
        Algebra.trdeg K (RatFunc K) = (1 : ℕ) := by sorry
