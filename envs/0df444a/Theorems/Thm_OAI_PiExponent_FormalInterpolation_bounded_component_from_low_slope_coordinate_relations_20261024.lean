-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_component_from_low_slope_coordinate_relations_20261024
-- name    : OAI.PiExponent.FormalInterpolation.bounded_component_from_low_slope_coordinate_relations_20261024
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:14:30.138114+00:00
-- url     : https://prove2.me/theorems/4c0b5dde-9c38-4bfd-8c3a-c86c67bf6a94
-- title:
--   Low-slope coordinate relations give a finite-colength component ideal
-- statement:
--   Given common-degree coordinate relations in Iˢ⁰ with strict lower-weight remainders and a strict slope gap, produce the target finite-colength component ideal. Choose k large enough that kq₀ + 1 < ks₀(ρ + ε), raise each relation to the kth power, and use the strict support bound to identify its top weighted component with Xᵢᵏⁿⁱ. The component ideal then contains a positive power of every coordinate, so its quotient is finite-dimensional over Complex. For d = 0 this finite-dimensionality reduces to that of MvPolynomial (Fin 0) Complex ≃ Complex; the numerical gap still supplies s and q. The child preserves the strict inequalities and common-degree hypothesis used by the reduction.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.bounded_component_from_low_slope_coordinate_relations_20261024
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (rho : Rat) (eps : Real)
    (s₀ : Nat) (hs₀ : 0 < s₀) (q₀ : Rat) (hq₀ : 0 < q₀)
    (hgap : (q₀ : Real) < (s₀ : Real) * ((rho : Real) + eps))
    (n : Fin d → Nat) (hn : ∀ i, 0 < n i)
    (hdegree : ∀ i, (n i : Rat) * w i = q₀)
    (f : Fin d → MvPolynomial (Fin d) Complex)
    (hrelation : ∀ i, MvPolynomial.X i ^ n i - f i ∈ I ^ s₀)
    (hsupport : ∀ i a, a ∈ (f i).support →
      ∑ j, (w j : Real) * (a j : Real) < (q₀ : Real)) :
    ∃ s : Nat, 0 < s ∧ ∃ q : Rat, 0 < q ∧
      (q : Real) + 1 < (s : Real) * ((rho : Real) + eps) ∧
      Module.Finite Complex
        (MvPolynomial (Fin d) Complex ⧸ Ideal.span (Set.range (fun (p :
          {g : MvPolynomial (Fin d) Complex //
            g ∈ I ^ s ∧ ∀ a ∈ g.support,
              ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
          MvPolynomial.weightedHomogeneousComponent
            (fun j => (w j : ℚ)) q p.1))) := by sorry
