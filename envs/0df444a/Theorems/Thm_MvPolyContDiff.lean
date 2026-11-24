-- Prove2me | Theorems.Thm_MvPolyContDiff
-- name    : MvPolyContDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T14:26:25.501035+00:00
-- url     : https://prove2.me/theorems/ace9f1a6-b368-4562-9b1e-aaa201173fd8
-- title:
--   Mv Poly Cont Diff: Mv Poly Cont Diff
-- statement:
--   A polynomial function on `EuclideanSpace ℝ (Fin n)` is `C^k` for every
--   smoothness exponent `k` (so in particular real-analytic).
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MvPolyContDiff.lean#L9-L16
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MvPolyContDiff.lean#L9-L16

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_MvPolyContDiff
set_option autoImplicit false
@[expose] public section
public section

theorem MvPolyContDiff {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (k : WithTop ℕ∞) :
    ContDiff ℝ k
      (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) := by sorry
