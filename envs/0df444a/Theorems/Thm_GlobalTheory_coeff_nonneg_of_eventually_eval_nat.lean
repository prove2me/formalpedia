-- Prove2me | Theorems.Thm_GlobalTheory_coeff_nonneg_of_eventually_eval_nat
-- name    : GlobalTheory.coeff_nonneg_of_eventually_eval_nat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:06:32.469597+00:00
-- url     : https://prove2.me/theorems/8f1c2e67-ef94-41d9-aebd-9dc0beb138a5
-- title:
--   Global Theory: coeff nonneg of eventually eval nat
-- statement:
--   The Global Theory construction uses the coeff nonneg of eventually eval nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L35-L40

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

theorem GlobalTheory.coeff_nonneg_of_eventually_eval_nat {P : ℚ[X]} {e : ℕ} (he : P.degree ≤ e)
    (h : ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ)) : 0 ≤ P.coeff e := by sorry
