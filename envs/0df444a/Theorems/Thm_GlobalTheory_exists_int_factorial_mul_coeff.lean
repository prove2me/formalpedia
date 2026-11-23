-- Prove2me | Theorems.Thm_GlobalTheory_exists_int_factorial_mul_coeff
-- name    : GlobalTheory.exists_int_factorial_mul_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:15:43.605902+00:00
-- url     : https://prove2.me/theorems/30c7c415-0114-46a1-b91c-5614100c30e2
-- title:
--   Global Theory: exists int factorial mul coeff
-- statement:
--   The Global Theory construction uses the exists int factorial mul coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L55-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L55-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module
open GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GlobalTheory.exists_int_factorial_mul_coeff {e : ℕ} {P : ℚ[X]} (he : P.degree ≤ e)
    (h : ∀ᶠ n : ℕ in atTop, ∃ z : ℤ, P.eval (n : ℚ) = z) :
    ∃ z : ℤ, (e.factorial : ℚ) * P.coeff e = z := by sorry
