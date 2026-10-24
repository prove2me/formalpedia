-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_aeval_pderiv_commute_of_generator
-- name    : OAI.PiExponent.FormalInterpolation.aeval_pderiv_commute_of_generator
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:09:35.602517+00:00
-- url     : https://prove2.me/theorems/5df33b67-aac5-4f08-9880-6c085aac83d2
-- title:
--   Evaluation commutes with a derivation from its generator values
-- statement:
--   For polynomial evaluation, evaluating the partial derivative agrees with applying a derivation after evaluation when the derivation sends the selected generator to one and every other generator to zero.

import Mathlib.Algebra.MvPolynomial.PDeriv

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.aeval_pderiv_commute_of_generator {σ R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [DecidableEq σ] (D : Derivation R S S) (g : σ → S) (p : MvPolynomial σ R) (i : σ) (hg : ∀ j, D (g j) = if j = i then 1 else 0) : MvPolynomial.aeval g (MvPolynomial.pderiv i p) = D (MvPolynomial.aeval g p) := by sorry
