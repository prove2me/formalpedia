-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_jet_kernel
-- name    : OAI.PiExponent.FormalInterpolation.finite_jet_kernel
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T13:45:37.745532+00:00
-- url     : https://prove2.me/theorems/9f4d3df2-2c7a-40a7-9769-0c15322e7f19
-- title:
--   More monomials than finite jet constraints yield a nonzero polynomial
-- statement:
--   If the finite allowed support region has more exponents than the total number of center-indexed jet constraints, then there is a nonzero polynomial supported in that region whose translated coefficients vanish at every required jet exponent.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.Data.Set.Card

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.finite_jet_kernel
    (n K : Nat) (W V : Fin n → Rat) (N : Nat) (a : Real)
    (c : Fin K → Fin n → Complex)
    (hSfinite : Set.Finite {m : Fin n →₀ Nat |
      (∑ i : Fin n, (m i : Real) * (W i : Real)) ≤ (N : Real)})
    (hTfinite : Set.Finite {b : Fin n →₀ Nat |
      (∑ i : Fin n, (b i : Real) * (V i : Real)) < a * (N : Real)})
    (hcard : Set.ncard {m : Fin n →₀ Nat |
      (∑ i : Fin n, (m i : Real) * (W i : Real)) ≤ (N : Real)} >
      K * Set.ncard {b : Fin n →₀ Nat |
      (∑ i : Fin n, (b i : Real) * (V i : Real)) < a * (N : Real)}) :
    ∃ F : MvPolynomial (Fin n) Complex,
      F ≠ 0 ∧ fibreContactSupportBound W N F ∧
        fibreContactJetVanishing c V (a * (N : Real)) F := by sorry
