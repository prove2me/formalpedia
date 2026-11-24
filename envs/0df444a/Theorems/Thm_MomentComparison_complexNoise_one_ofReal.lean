-- Prove2me | Theorems.Thm_MomentComparison_complexNoise_one_ofReal
-- name    : MomentComparison.complexNoise_one_ofReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:51:08.446731+00:00
-- url     : https://prove2.me/theorems/cb30de43-6895-44bf-83a4-9389dc6a98e9
-- title:
--   Moment Comparison: complex Noise one of Real
-- statement:
--   The Moment Comparison construction uses the complex Noise one of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/NoisePolynomial.lean#L146-L150
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/NoisePolynomial.lean#L146-L150

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

theorem MomentComparison.complexNoise_one_ofReal {n : ℕ} (f : Cube n → ℝ) (x : Cube n) :
    complexNoise 1 (fun y => (f y : ℂ)) x = (f x : ℂ) := by sorry
