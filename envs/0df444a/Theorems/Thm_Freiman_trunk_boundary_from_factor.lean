-- Prove2me | Theorems.Thm_Freiman_trunk_boundary_from_factor
-- name    : Freiman.trunk_boundary_from_factor
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:37:04.564032+00:00
-- url     : https://prove2.me/theorems/348eb85f-2d50-4a24-905b-e0b97545fd67
-- title:
--   trunk boundary from factor
-- statement:
--   The original antisymmetric H11/H0 polynomial is strictly positive when r<s because all quotient coefficients are negative. Thus its nonpositive value forces equality, using exact source field enclosures.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_boundary_from_factor (hf : ∀ (P : CertPoly22), (∀ i j : Fin 3, P i j = certFieldScale (-1) (P j i)) → ∀ r s : ℝ, certPolyEval P r s = (r-s)*(certFieldVal (P 1 0)+certFieldVal (P 2 0)*(r+s)+certFieldVal (P 2 1)*r*s))
    (hb : ∀ z : CertField, (certFieldLower z : ℝ) ≤ certFieldVal z)
    (hscale : ∀ (q : ℚ) (z : CertField), certFieldVal (certFieldScale q z) = (q : ℝ)*certFieldVal z)
    (hc : trunkBoundaryCertificateValid) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ s)
    (hp : certPolyEval trunkBoundaryPolynomial r s ≤ 0) :
    r = s := by
  sorry
