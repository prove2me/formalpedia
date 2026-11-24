-- Prove2me | Theorems.Thm_MomentComparison_complexNoise_ofReal
-- name    : MomentComparison.complexNoise_ofReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:20:56.742326+00:00
-- url     : https://prove2.me/theorems/34d957af-f246-4111-bcb2-342a53f98d1a
-- title:
--   Moment Comparison: complex Noise of Real
-- statement:
--   Walsh level `k` acquires the factor `w^k` under complex noise.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/NoisePolynomial.lean#L135-L144
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/NoisePolynomial.lean#L135-L144

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

theorem MomentComparison.complexNoise_ofReal {n : ℕ} (w : ℂ) (f : Cube n → ℝ) (x : Cube n) :
    complexNoise w (fun y => (f y : ℂ)) x =
      ∑ s : Finset (Fin n), (cubeAverage (fun y => f y * walsh s y) : ℂ) *
        (w ^ s.card * (walsh s x : ℂ)) := by sorry
