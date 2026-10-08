-- Prove2me | Theorems.Thm_OAI_PiExponent_finite_extension_derivation_ne_simple_pole
-- name    : OAI.PiExponent.finite_extension_derivation_ne_simple_pole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:27:03.489572+00:00
-- url     : https://prove2.me/theorems/900d5323-eb75-4496-883d-ee33484a3867
-- title:
--   A finite algebraic extension cannot supply a logarithmic antiderivative
-- statement:
--   Let $K$ have characteristic zero and let $E$ be a finite-dimensional extension of $K(X)$ in a compatible tower over $K$. Let $d$ and $D$ be compatible $K$-derivations of $K(X)$ and $E$, with $d(X)=1$. For every $x\in E$ and nonzero $c\in K$, $D(x)$ is not the image of $c/X$ in $E$. Thus passing to this finite extension does not remove the simple-pole obstruction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LogarithmicObstruction.lean#L160-L182

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

theorem OAI.PiExponent.finite_extension_derivation_ne_simple_pole
    {K E : Type*} [Field K] [CharZero K] [Field E]
    [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    [FiniteDimensional (RatFunc K) E]
    (d : Derivation K (RatFunc K) (RatFunc K)) (D : Derivation K E E)
    (hdX : d RatFunc.X = 1)
    (hcompat : ∀ a : RatFunc K,
      D (algebraMap (RatFunc K) E a) = algebraMap (RatFunc K) E (d a))
    (x : E) {c : K} (hc : c ≠ 0) :
    D x ≠ algebraMap (RatFunc K) E (RatFunc.C c / RatFunc.X) := by sorry
