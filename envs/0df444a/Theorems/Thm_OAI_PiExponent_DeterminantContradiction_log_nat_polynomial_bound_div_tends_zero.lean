-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_log_nat_polynomial_bound_div_tends_zero
-- name    : OAI.PiExponent.DeterminantContradiction.log_nat_polynomial_bound_div_tends_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T18:04:21.939682+00:00
-- url     : https://prove2.me/theorems/04379563-4c66-4e69-975c-0832f724c849
-- title:
--   Logarithm of an eventually polynomially bounded natural function is sublinear
-- statement:
--   If a natural-valued function is eventually positive and bounded above by a positive constant times a fixed power of H+1, then its logarithm divided by H tends to zero.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology

theorem OAI.PiExponent.DeterminantContradiction.log_nat_polynomial_bound_div_tends_zero (f : Real → Nat) (C : Real) (N : Nat) (hC : 0 < C) (hbound : ∀ᶠ H : Real in atTop, 0 < (f H : Real) ∧ (f H : Real) ≤ C * (H + 1) ^ N) : Tendsto (fun H : Real => Real.log (f H : Real) / H) atTop (𝓝 0) := by sorry
