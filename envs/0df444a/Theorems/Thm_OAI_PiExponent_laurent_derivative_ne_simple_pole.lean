-- Prove2me | Theorems.Thm_OAI_PiExponent_laurent_derivative_ne_simple_pole
-- name    : OAI.PiExponent.laurent_derivative_ne_simple_pole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:27:07.258272+00:00
-- url     : https://prove2.me/theorems/882b7f92-f82e-4a38-831a-4f481bb14149
-- title:
--   A Laurent-series derivative cannot be a nonzero simple pole
-- statement:
--   For any field $K$, Laurent series $f$ over $K$, and nonzero scalar $c\in K$, the derivative of $f$ is not the Laurent monomial $cX^{-1}$. The residue of a derivative vanishes, while the residue of this simple pole is $c$.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LogarithmicObstruction.lean#L19-L24

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

theorem OAI.PiExponent.laurent_derivative_ne_simple_pole {K : Type*} [Field K]
    (f : K⸨X⸩) {c : K} (hc : c ≠ 0) :
    LaurentSeries.derivative K f ≠ HahnSeries.single (-1) c := by sorry
