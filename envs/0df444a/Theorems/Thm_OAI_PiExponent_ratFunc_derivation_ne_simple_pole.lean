-- Prove2me | Theorems.Thm_OAI_PiExponent_ratFunc_derivation_ne_simple_pole
-- name    : OAI.PiExponent.ratFunc_derivation_ne_simple_pole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:27:31.26664+00:00
-- url     : https://prove2.me/theorems/d8e59d47-5001-461a-bb2e-b44272f5fa4e
-- title:
--   A rational-function derivative cannot be a nonzero simple pole
-- statement:
--   Let $K$ be a field of characteristic zero, and let $D$ be a $K$-derivation of $K(X)$ satisfying $D(X)=1$. For every $r\in K(X)$ and every nonzero $c\in K$,
--   $$D(r)\ne c/X.$$
--   This obstructs rational antiderivatives of a nonzero logarithmic differential.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LogarithmicObstruction.lean#L75-L99

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

theorem OAI.PiExponent.ratFunc_derivation_ne_simple_pole {K : Type*} [Field K] [CharZero K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hDX : D RatFunc.X = 1) (r : RatFunc K) {c : K} (hc : c ≠ 0) :
    D r ≠ RatFunc.C c / RatFunc.X := by sorry
