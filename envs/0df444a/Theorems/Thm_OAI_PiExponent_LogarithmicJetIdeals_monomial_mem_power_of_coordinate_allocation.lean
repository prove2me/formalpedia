-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_monomial_mem_power_of_coordinate_allocation
-- name    : OAI.PiExponent.LogarithmicJetIdeals.monomial_mem_power_of_coordinate_allocation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T20:34:55.42556+00:00
-- url     : https://prove2.me/theorems/1a419de3-e28a-4f48-8f9b-a28309d62d9e
-- title:
--   Coordinate allocation gives monomial ideal-power membership
-- statement:
--   A finitely supported allocation of n generator factors, bounded coordinatewise by the monomial exponents, gives membership in the nth power of the coordinate-generator ideal.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.monomial_mem_power_of_coordinate_allocation
    {m : ℕ} (e : Fin (m + 1) → ℕ) (n : ℕ)
    (d k : Fin (m + 1) →₀ ℕ)
    (hksum : k.sum (fun _ x => x) = n)
    (hdiv : ∀ i, k i * e i ≤ d i) :
    MvPolynomial.monomial d (1 : ℂ) ∈
      (Ideal.span (Set.range (fun i : Fin (m + 1) =>
        MvPolynomial.X i ^ e i)) : Ideal (MvPolynomial (Fin (m + 1)) ℂ)) ^ n := by
  sorry
