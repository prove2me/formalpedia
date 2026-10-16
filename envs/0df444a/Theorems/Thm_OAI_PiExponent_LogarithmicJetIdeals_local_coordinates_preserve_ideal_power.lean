-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_local_coordinates_preserve_ideal_power
-- name    : OAI.PiExponent.LogarithmicJetIdeals.local_coordinates_preserve_ideal_power
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T21:18:48.864927+00:00
-- url     : https://prove2.me/theorems/f0808af1-9d2e-4474-afb9-5bfc535c6452
-- title:
--   Local coordinate substitution transports ideal powers
-- statement:
--   The inverse polynomial coordinate substitution transports membership in a coordinate monomial ideal power to membership in the corresponding local logarithmic jet ideal power.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinates
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.local_coordinates_preserve_ideal_power
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (n : ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hQ : localCoordinatePolynomial c T P ∈
      Ideal.span (Set.range (fun i : Fin (m + 1) =>
        (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) ℂ) ^ e i)) ^ n) :
    P ∈ localJetIdeal c T e ^ n := by sorry
