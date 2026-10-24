-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_origin_support_powers_20261023_22
-- name    : OAI.PiExponent.FormalInterpolation.origin_support_powers_20261023_22
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T18:33:25.968524+00:00
-- url     : https://prove2.me/theorems/0bb97c20-6d01-41cf-85ef-1445f7227514
-- title:
--   Common zeros only at the origin imply coordinate powers
-- statement:
--   If the common zero set of a finite family of complex polynomials is contained in the origin, a positive power of each coordinate lies in the ideal they generate. For `d = 0` the conclusion is vacuous. The independent proof route is the strong Nullstellensatz, placing each coordinate in the radical and extracting a positive power. This supplies the final algebraic-geometric step used by the parent.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

theorem OAI.PiExponent.FormalInterpolation.origin_support_powers_20261023_22
    {d m : Nat} (q : Fin m → MvPolynomial (Fin d) Complex)
    (hzero : ∀ x : Fin d → Complex,
      (∀ j : Fin m, MvPolynomial.eval x (q j) = 0) →
      ∀ i : Fin d, x i = 0) :
    (∀ i : Fin d, ∃ N : Nat,
      0 < N ∧ (MvPolynomial.X i) ^ N ∈ Ideal.span (Set.range q)) := by sorry
