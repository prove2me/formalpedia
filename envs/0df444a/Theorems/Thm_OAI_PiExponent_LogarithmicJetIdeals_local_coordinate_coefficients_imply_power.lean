-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_coordinate_coefficients_imply_power
-- name    : OAI.PiExponent.LogarithmicJetIdeals.local_coordinate_coefficients_imply_power
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T21:18:18.299253+00:00
-- url     : https://prove2.me/theorems/5c7c9227-cf71-4a46-9b40-30a64cac411a
-- title:
--   Local-coordinate coefficient staircase implies a monomial ideal power
-- statement:
--   For positive generator exponents, vanishing of every coefficient whose natural-quotient sum is below n implies membership in the nth power of the coordinate monomial ideal.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.local_coordinate_coefficients_imply_power
    {m : ℕ} (e : Fin (m + 1) → ℕ)
    (he : ∀ i, 0 < e i) (n : ℕ)
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoeff : ∀ a : Fin (m + 1) → ℕ,
      (∑ i, a i / e i : ℕ) < n →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a) Q = 0) :
    Q ∈ Ideal.span (Set.range (fun i : Fin (m + 1) =>
      (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) ℂ) ^ e i)) ^ n := by sorry
