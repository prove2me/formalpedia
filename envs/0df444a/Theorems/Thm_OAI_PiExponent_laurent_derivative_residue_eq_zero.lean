-- Prove2me | Theorems.Thm_OAI_PiExponent_laurent_derivative_residue_eq_zero
-- name    : OAI.PiExponent.laurent_derivative_residue_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:27:02.889021+00:00
-- url     : https://prove2.me/theorems/ceebddb3-ff06-4361-959d-7adce407d563
-- title:
--   A Laurent-series derivative has zero residue
-- statement:
--   For any field $K$ and formal Laurent series $f$ over $K$, the coefficient of $X^{-1}$ in its formal derivative is zero. This is the residue obstruction to a Laurent series being a derivative.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LogarithmicObstruction.lean#L15-L17

import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Trace.Defs
import Mathlib.Tactic


namespace OAI
namespace PiExponent
end PiExponent
end OAI
open scoped LaurentSeries Matrix
open OAI.PiExponent

theorem OAI.PiExponent.laurent_derivative_residue_eq_zero {K : Type*} [Field K]
    (f : K⸨X⸩) : (LaurentSeries.derivative K f).coeff (-1) = 0 := by sorry
