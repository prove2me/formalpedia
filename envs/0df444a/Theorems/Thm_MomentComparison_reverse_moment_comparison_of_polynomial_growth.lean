-- Prove2me | Theorems.Thm_MomentComparison_reverse_moment_comparison_of_polynomial_growth
-- name    : MomentComparison.reverse_moment_comparison_of_polynomial_growth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:05:50.389062+00:00
-- url     : https://prove2.me/theorems/8330edda-1a92-4722-922e-71b46f917c2b
-- title:
--   Moment Comparison: reverse moment comparison of polynomial growth
-- statement:
--   Polynomial growth transfers a contraction on a complex set to a
--   reverse moment comparison at the point `1`.
--
--   Source: https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Upper.lean#L194-L218
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/Upper.lean#L194-L218

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

theorem MomentComparison.reverse_moment_comparison_of_polynomial_growth
    {n d : ℕ} {p q L : ℝ} (hp : 2 < p) (hpq : p.HolderConjugate q) (hL : 0 ≤ L)
    {V : Set ℂ} (f : Cube n → ℝ) (F : ℂ → Cube n → ℂ)
    (hFone : ∀ x, F 1 x = (f x : ℂ))
    (hcontract : ∀ w ∈ V, complexMomentNorm p (F w) ≤
      complexMomentNorm q (fun x => (f x : ℂ)))
    (hpoly : ∀ g : Cube n → ℂ, ∃ P : Polynomial ℂ, P.natDegree ≤ d ∧
      ∀ w, P.eval w = (∑ x, F w x * g x) / (2 : ℂ) ^ n)
    (hgrowth : ∀ (P : Polynomial ℂ), P.natDegree ≤ d → ∀ M : ℝ, 0 ≤ M →
      (∀ w ∈ V, ‖P.eval w‖ ≤ M) → ‖P.eval 1‖ ≤ L ^ d * M) :
    complexMomentNorm p (fun x => (f x : ℂ)) ≤
      L ^ d * complexMomentNorm q (fun x => (f x : ℂ)) := by sorry
