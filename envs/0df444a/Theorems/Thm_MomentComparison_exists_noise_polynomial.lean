-- Prove2me | Theorems.Thm_MomentComparison_exists_noise_polynomial
-- name    : MomentComparison.exists_noise_polynomial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:51:15.467663+00:00
-- url     : https://prove2.me/theorems/fcaeb5c3-5f5f-4775-bbb9-47a8fbe02d69
-- title:
--   Moment Comparison: exists noise polynomial
-- statement:
--   Pairing the noise evolution of a degree-`d` function with any fixed function
--   gives a scalar polynomial of degree at most `d`.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/NoisePolynomial.lean#L154-L188
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/NoisePolynomial.lean#L154-L188

module
public import Definitions.Def_MomentComparison_Walsh
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_NoisePolynomial
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison
open Finset

theorem MomentComparison.exists_noise_polynomial {n d : ℕ} (f : Cube n → ℝ) (hf : HasDegreeLE f d)
    (g : Cube n → ℂ) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ d ∧ ∀ w : ℂ,
      P.eval w = (∑ x, complexNoise w (fun y => (f y : ℂ)) x * g x) / (2 : ℂ) ^ n := by sorry
