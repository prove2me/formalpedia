-- Prove2me | Theorems.Thm_MomentComparison_moment_comparison_of_conjugate
-- name    : MomentComparison.moment_comparison_of_conjugate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:03:54.387582+00:00
-- url     : https://prove2.me/theorems/d7000165-cdac-436c-823b-94f84d32558e
-- title:
--   Moment Comparison: moment comparison of conjugate
-- statement:
--   A reverse comparison between conjugate exponents yields a bound at `(2, 1)`.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Upper.lean#L56-L124
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Upper.lean#L56-L124

module
public import Definitions.Def_MomentComparison_Pairing
public import Definitions.Def_MomentComparison_Conformal
public import Definitions.Def_MomentComparison_Hypercontractivity
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.Real.ConjExponents
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Upper
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison

theorem MomentComparison.moment_comparison_of_conjugate {n d : ℕ} {p L : ℝ} (hp : 2 < p)
    (hL : 0 < L) (f : Cube n → ℝ)
    (hReverse : complexMomentNorm p (fun x => (f x : ℂ)) ≤
      L ^ d * complexMomentNorm (p / (p - 1)) (fun x => (f x : ℂ))) :
    Real.sqrt (cubeAverage fun x => f x ^ 2) ≤
      (L ^ (p / (2 * (p - 2)))) ^ d * cubeAverage (fun x => |f x|) := by sorry
