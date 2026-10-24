-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_jet_selector_exists_repair8_b4ae670f_709b_4665_8d77_1253c6fa8d68
-- name    : OAI.PiExponent.FormalInterpolation.jet_selector_exists_repair8_b4ae670f_709b_4665_8d77_1253c6fa8d68
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T16:48:34.37341+00:00
-- url     : https://prove2.me/theorems/7938130e-f9a9-4ef0-9e94-27566f2af69d
-- title:
--   Separating selectors for finite Taylor jets
-- statement:
--   For each center j and exponent α, construct a polynomial whose bounded translated coefficient is one at (j, α) and zero at every other bounded jet. If α has degree greater than D, the zero polynomial meets the conditions because no bounded β can equal α. Otherwise prescribe the monomial jet at j and zero jets elsewhere. This removes the jet-separation step from the parent. The proof route is to identify coefficients through degree D with classes modulo the (D+1)st power of the point maximal ideal, show distinct point ideals are comaximal using injectivity of c, and apply the finite Chinese remainder theorem to their powers. The case D = 0 is the value-interpolation case; an empty J makes the universally quantified selector condition vacuous. The remaining core obligation is formalizing the local-coordinate correspondence and powered-ideal CRT application.

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Complex.Basic
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.jet_selector_exists_repair8_b4ae670f_709b_4665_8d77_1253c6fa8d68
    {n : Nat} {J : Type} [Fintype J] [DecidableEq J]
    (c : J → Fin n → Complex) (hc : Function.Injective c)
    (D : Nat) (j : J) (α : Fin n →₀ Nat) :
    ∃ E : MvPolynomial (Fin n) Complex,
      ∀ (k : J) (β : Fin n →₀ Nat),
        (∑ i : Fin n, β i) ≤ D →
        (MvPolynomial.aeval
          (fun i : Fin n => MvPolynomial.C (c k i) + MvPolynomial.X i) E).coeff β
          = if k = j ∧ β = α then 1 else 0 := by sorry
