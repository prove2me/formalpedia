-- Prove2me | Theorems.Thm_MomentComparison_complexNoise_cons
-- name    : MomentComparison.complexNoise_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:17:25.689331+00:00
-- url     : https://prove2.me/theorems/c0ce79ee-21d7-4731-9e5a-9e408239dc8f
-- title:
--   Moment Comparison: complex Noise cons
-- statement:
--   The Moment Comparison construction uses the complex Noise cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/NoisePolynomial.lean#L28-L35
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/NoisePolynomial.lean#L28-L35

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

theorem MomentComparison.complexNoise_cons {n : ℕ} (w : ℂ) (f : Cube (n + 1) → ℂ) (b : Bool) (x : Cube n) :
    complexNoise w f (Fin.cons b x) =
      (complexNoise w (fun y => f (Fin.cons true y)) x +
        complexNoise w (fun y => f (Fin.cons false y)) x) / 2 +
      (if b then 1 else -1) * w *
        (complexNoise w (fun y => f (Fin.cons true y)) x -
          complexNoise w (fun y => f (Fin.cons false y)) x) / 2 := by sorry
