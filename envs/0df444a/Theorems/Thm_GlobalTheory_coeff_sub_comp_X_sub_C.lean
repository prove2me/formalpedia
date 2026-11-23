-- Prove2me | Theorems.Thm_GlobalTheory_coeff_sub_comp_X_sub_C
-- name    : GlobalTheory.coeff_sub_comp_X_sub_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:58:11.123802+00:00
-- url     : https://prove2.me/theorems/39e714aa-5c3c-4d23-b768-7bba407b41c8
-- title:
--   Global Theory: coeff sub comp X sub C
-- statement:
--   The Global Theory construction uses the coeff sub comp X sub C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/XSmulMemWeightedHomogeneousSubmodule.lean#L662-L679
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/XSmulMemWeightedHomogeneousSubmodule.lean#L662-L679

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter
open GlobalTheory
open DirectSum Module GradedHilbert
variable {k : Type*} [Field k] {M' M M'' : Type*} [AddCommGroup M'] [Module k M']
  [AddCommGroup M] [Module k M] [AddCommGroup M''] [Module k M'']
variable {ι : Type*} [Module (MvPolynomial ι k) M'] [IsScalarTower k (MvPolynomial ι k) M']
  [Module (MvPolynomial ι k) M] [IsScalarTower k (MvPolynomial ι k) M]
  [Module (MvPolynomial ι k) M''] [IsScalarTower k (MvPolynomial ι k) M'']

theorem GlobalTheory.coeff_sub_comp_X_sub_C {K : Type*} [Field K] (P : K[X]) (r : K) (e : ℕ)
    (hP : P.degree ≤ (e + 1 : ℕ)) :
    (P - P.comp (X - C r)).degree < (e + 1 : ℕ) ∧
      (P - P.comp (X - C r)).coeff e = r * (e + 1) * P.coeff (e + 1) := by sorry
