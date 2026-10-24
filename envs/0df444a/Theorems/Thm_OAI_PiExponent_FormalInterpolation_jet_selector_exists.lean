-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_jet_selector_exists
-- name    : OAI.PiExponent.FormalInterpolation.jet_selector_exists
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:52:28.687559+00:00
-- url     : https://prove2.me/theorems/5418326e-4ebe-4d13-88c9-dfab39c69df2
-- title:
--   Separating selectors for finite Taylor jets
-- statement:
--   For each center and exponent, construct a polynomial whose translated coefficient is one at that jet and zero at every other jet through total degree D. The explicit decidable-equality assumption makes the conditional in the statement well-formed. A proof route uses pairwise comaximal powers of the distinct point maximal ideals, the finite Chinese remainder theorem, and the correspondence between bounded translated coefficients and local quotient classes. The total-degree bound is retained, including the D = 0 case.

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Complex.Basic
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.jet_selector_exists
    {n : Nat} {J : Type} [Fintype J] [DecidableEq J]
    (c : J → Fin n → Complex) (hc : Function.Injective c)
    (D : Nat) (j : J) (α : Fin n →₀ Nat) :
    ∃ E : MvPolynomial (Fin n) Complex,
      ∀ (k : J) (β : Fin n →₀ Nat),
        (∑ i : Fin n, β i) ≤ D →
        (MvPolynomial.aeval
          (fun i : Fin n => MvPolynomial.C (c k i) + MvPolynomial.X i) E).coeff β
          = if k = j ∧ β = α then 1 else 0 := by sorry
