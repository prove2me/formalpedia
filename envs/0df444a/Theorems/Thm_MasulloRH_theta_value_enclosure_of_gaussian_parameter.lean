-- Prove2me | Theorems.Thm_MasulloRH_theta_value_enclosure_of_gaussian_parameter
-- name    : MasulloRH.theta_value_enclosure_of_gaussian_parameter
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T09:28:24.989092+00:00
-- url     : https://prove2.me/theorems/18873aee-887a-409b-b96d-6e0f49265020
-- title:
--   A finite polynomial enclosure for the full logarithmic Gaussian theta sum
-- statement:
--   For a real input \(x\), enclose \(q=\exp(-\pi e^{2x})\) by \(0\le L\le q\le U<1\). For an integer cutoff \(K\ge0\) let
--
--   \[
--    B(a,b)=2\sum_{k=1}^{K}\left(a^{k^2}-3b^{4k^2}+2a^{16k^2}\right),
--    \qquad E=\frac{12U^{(K+1)^2}}{1-U^{2K+3}} .
--   \]
--
--   The canonical infinite theta sum at \(x\) is real and lies in \([B(L,U)-E,\ B(U,L)+E]\). Rational \(L,U\) give rational output endpoints. This supplies a direct value enclosure for the compact height-two grid. Applying the same statement at \(-x-\log 4\) and multiplying by \(e^{-x}/2\) supplies the reflected enclosure.
-- source:
--   Developed for the explicit height-two shared grid, https://prove2.me/theorems/a1982f8d-9d4a-4b3f-88ac-3a2cdaee2ead . The infinite-sum truncation bound used is https://prove2.me/theorems/2e9c99f7-cd06-43f7-a85b-f4d2cc422151 .

import Theorems.Thm_MasulloRH_theta_gaussian_truncation_error
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MasulloRH.GaussianApproximation
open scoped BigOperators ComplexConjugate

theorem MasulloRH.theta_value_enclosure_of_gaussian_parameter (K : ℕ) (x L U : ℝ) (hL : 0 ≤ L)
    (hl : L ≤ Real.exp (-Real.pi * (Real.exp x)^2))
    (hu : Real.exp (-Real.pi * (Real.exp x)^2) ≤ U) (hU : U < 1) :
    let B (a b : ℝ) := 2 * ∑ n ∈ Finset.range K,
      (a ^ ((n+1)^2) - 3*b ^ (4*(n+1)^2) + 2*a ^ (16*(n+1)^2))
    let E := 12 * U ^ ((K+1)^2) / (1 - U ^ (2*K+3))
    (theta x).im = 0 ∧ B L U - E ≤ (theta x).re ∧ (theta x).re ≤ B U L + E := by sorry
