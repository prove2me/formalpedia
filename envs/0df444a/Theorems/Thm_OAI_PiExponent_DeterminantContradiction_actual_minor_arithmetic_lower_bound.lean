-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_arithmetic_lower_bound
-- name    : OAI.PiExponent.DeterminantContradiction.actual_minor_arithmetic_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-07T19:29:55.017604+00:00
-- url     : https://prove2.me/theorems/bd566832-025d-4e8f-95cf-c42d37b6db92
-- title:
--   Arithmetic lower bound for every nonzero actual interpolation minor
-- statement:
--   For any fixed admissible family $d$, every positive height $H$, and every selection $s$ of columns indexed by the rows, a nonzero selected minor satisfies
--
--   $$-(1-b_d(H))-e_{\rm ar}(d)\le
--   \frac{\log\|\det M_d(H)[s]\|}{\#\operatorname{Rows}_d(H)\,H}.$$
--
--   Here $b_d(H)$ is the actual mean row weight and $e_{\rm ar}(d)$ is the fixed arithmetic error. The nonvanishing assumption is explicit; this theorem does not construct a nonzero minor. It supplies the arithmetic side of the determinant comparison for whichever minor the interpolation argument selects.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/DeterminantContradiction.lean#L74-L86

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily

open Filter Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.DeterminantContradiction.actual_minor_arithmetic_lower_bound {nu : ℝ} (d : FixedData nu)
    (H : ℝ) (hH : 0 < H) (selection : Row d H → Column d H)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    -(1 - actualMean d H) - d.arithmeticError ≤
      Real.log ‖(actualMinor d H selection).det‖ /
        ((actualRowCount d H : ℝ) * H) := by sorry
