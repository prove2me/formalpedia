-- Prove2me | Theorems.Thm_OAI_PiExponent_ratFunc_derivation_polynomial
-- name    : OAI.PiExponent.ratFunc_derivation_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:27:03.233074+00:00
-- url     : https://prove2.me/theorems/6eb328e2-2714-451c-8dbb-f4068e3357c6
-- title:
--   A normalized rational-function derivation differentiates polynomials
-- statement:
--   Let $K$ be a field and let $D$ be a $K$-derivation of its rational-function field with $D(X)=1$. For every polynomial $p\in K[X]$, applying $D$ to the canonical image of $p$ gives the canonical image of its formal derivative $p'$. This identifies the restriction of $D$ to the polynomial subalgebra.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LogarithmicObstruction.lean#L68-L73

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
open Polynomial
open OAI.PiExponent

theorem OAI.PiExponent.ratFunc_derivation_polynomial {K : Type*} [Field K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hDX : D RatFunc.X = 1) (p : K[X]) :
    D (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (derivative p) := by sorry
