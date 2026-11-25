-- Prove2me | Theorems.Thm_MainTheorem
-- name    : MainTheorem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:07:26.911159+00:00
-- url     : https://prove2.me/theorems/555dff9a-9c03-53ad-99c4-26f6e56fc78a
-- title:
--   Main Theorem: Main Theorem
-- statement:
--   The paper's Theorem 1.1: for `n ≥ 3` and `p ≥ n - 1/13`, every real
--   polynomial on `ℝ^n` annihilated by `E_p` is affine.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MainTheorem.lean#L14-L33
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MainTheorem.lean#L14-L33

module
public import Definitions.Def_PHarmonicPoly_HomogeneousCase
public import Definitions.Def_PHarmonicPoly_TopComponent
public import Definitions.Def_PHarmonicPoly_TopComponentNeZero
public import Definitions.Def_PHarmonicPoly_AffineOfTotalDegreeLeOne
public import Definitions.Def_PHarmonicPoly_EpOpEvalPoly
public import Definitions.Def_PHarmonicPoly_MainTheorem
public import Theorems.Thm_AffineOfTotalDegreeLeOne
public import Theorems.Thm_EpOpEvalPoly
public import Theorems.Thm_HomogeneousCase
public import Theorems.Thm_TopComponent
public import Theorems.Thm_TopComponentNeZero

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem MainTheorem {n : ℕ} (hn : 3 ≤ n) {p : ℝ} (hp : (n : ℝ) - 1 / 13 ≤ p)
    (P : MvPolynomial (Fin n) ℝ)
    (hE : ∀ x : EuclideanSpace ℝ (Fin n),
      EpOp p (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x = 0) :
    ∃ (w : EuclideanSpace ℝ (Fin n)) (c : ℝ), ∀ x : EuclideanSpace ℝ (Fin n),
      MvPolynomial.eval (fun i => x i) P = inner ℝ w x + c := by sorry
