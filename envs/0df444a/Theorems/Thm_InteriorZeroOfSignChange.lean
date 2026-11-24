-- Prove2me | Theorems.Thm_InteriorZeroOfSignChange
-- name    : InteriorZeroOfSignChange
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T15:15:26.175847+00:00
-- url     : https://prove2.me/theorems/7aa5ca65-95a6-45e7-9c84-a203811600e7
-- title:
--   Interior Zero Of Sign Change: Interior Zero Of Sign Change
-- statement:
--   A strict-interior intermediate value theorem. If `D : ℝ → ℝ` is continuous
--   and its values at `a < b` have opposite signs, then `D` vanishes at some point
--   strictly between `a` and `b`. Mathlib's `intermediate_value_Icc` gives a zero in
--   the closed interval; the sign hypothesis rules out both endpoints.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/InteriorZeroOfSignChange.lean#L11-L38
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/InteriorZeroOfSignChange.lean#L11-L38

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_InteriorZeroOfSignChange
set_option autoImplicit false
@[expose] public section
public section

theorem InteriorZeroOfSignChange (D : ℝ → ℝ) (hD : Continuous D) (a b : ℝ)
    (hab : a < b) (hsign : D a * D b < 0) : ∃ z, a < z ∧ z < b ∧ D z = 0 := by sorry
