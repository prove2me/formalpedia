-- Prove2me | Theorems.Thm_OAI_PiExponent_derivation_trace_of_basis
-- name    : OAI.PiExponent.derivation_trace_of_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:27:04.134541+00:00
-- url     : https://prove2.me/theorems/eb5f8e83-310b-408e-bc63-a929dc92f7af
-- title:
--   Compatible derivations commute with field trace
-- statement:
--   Let $k\subseteq F\subseteq E$ be a compatible field tower, and assume a finite $F$-basis of $E$ is given. If $k$-derivations $d$ on $F$ and $D$ on $E$ agree on the embedded copy of $F$, then every $x\in E$ satisfies
--   $$d(\operatorname{Tr}_{E/F}(x))=\operatorname{Tr}_{E/F}(D(x)).$$
--   This relates differentiation in a finite extension to differentiation in its base field.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LogarithmicObstruction.lean#L126-L158

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

theorem OAI.PiExponent.derivation_trace_of_basis
    {k F E ι : Type*} [Field k] [Field F] [Field E] [Fintype ι]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    (d : Derivation k F F) (D : Derivation k E E)
    (hcompat : ∀ a : F, D (algebraMap F E a) = algebraMap F E (d a))
    (b : Module.Basis ι F E) (x : E) :
    d (Algebra.trace F E x) = Algebra.trace F E (D x) := by sorry
