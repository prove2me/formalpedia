-- Prove2me | Theorems.Thm_Freiman_trunk_diagonal_polynomial_from_corners
-- name    : Freiman.trunk_diagonal_polynomial_from_corners
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:38:03.010094+00:00
-- url     : https://prove2.me/theorems/65b25e76-eed8-477f-804f-b8534bb3a50a
-- title:
--   trunk diagonal polynomial from corners
-- statement:
--   Combine source factorization, the signed bilinear corner rule and the selected weak diagonal half-plane, including r=s.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_diagonal_polynomial_from_corners (hf : ∀ (P : CertPoly22), (∀ i j : Fin 3, P i j = certFieldScale (-1) (P j i)) → ∀ r s : ℝ, certPolyEval P r s = (r-s)*(certFieldVal (P 1 0)+certFieldVal (P 2 0)*(r+s)+certFieldVal (P 2 1)*r*s))
    (hb : ∀ (R : CertRectangle) (A B D : ℝ), certRectangleValid R → (∀ i j : Fin 2, 0 < A+B*((trunkCorner R.r0 R.r1 i : ℝ)+trunkCorner R.s0 R.s1 j)+D*trunkCorner R.r0 R.r1 i*trunkCorner R.s0 R.s1 j) → ∀ r s : ℝ, certRectangleMem R r s → 0 < A+B*(r+s)+D*r*s)
    (C : TrunkCatalog) (w : TrunkWitness) (hw : trunkWitnessValid C w) (hn : w.diagonal ≠ 0)
    (hc : ∀ i j : Fin 2, 0 < (w.diagonal : ℝ)*(certFieldVal (trunkPolynomial C w 1 0)+certFieldVal (trunkPolynomial C w 2 0)*((trunkCorner w.rectangle.r0 w.rectangle.r1 i : ℝ)+trunkCorner w.rectangle.s0 w.rectangle.s1 j)+certFieldVal (trunkPolynomial C w 2 1)*trunkCorner w.rectangle.r0 w.rectangle.r1 i*trunkCorner w.rectangle.s0 w.rectangle.s1 j))
    (r s : ℝ) (hm : certRectangleMem w.rectangle r s) (hs : 0 ≤ (w.diagonal : ℝ)*(r-s)) :
    0 ≤ certPolyEval (trunkPolynomial C w) r s := by
  sorry
