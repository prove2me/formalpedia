-- Prove2me | Theorems.Thm_OAI_PiExponent_derivation_intermediate_smul
-- name    : OAI.PiExponent.derivation_intermediate_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:27:02.769652+00:00
-- url     : https://prove2.me/theorems/eae15bf7-e1d6-4e5c-b187-1c2076824c02
-- title:
--   Compatible derivations obey the intermediate-field product rule
-- statement:
--   Let $k\subseteq F\subseteq E$ be a compatible tower of fields, with compatible $k$-derivations $d:F\to F$ and $D:E\to E$. For every $a\in F$ and $z\in E$,
--   $$D(a\cdot z)=d(a)\cdot z+a\cdot D(z).$$
--   Here multiplication by an element of $F$ uses its given action on $E$.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LogarithmicObstruction.lean#L101-L109

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

theorem OAI.PiExponent.derivation_intermediate_smul
    {k F E : Type*} [Field k] [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    (d : Derivation k F F) (D : Derivation k E E)
    (hcompat : ∀ a : F, D (algebraMap F E a) = algebraMap F E (d a))
    (a : F) (z : E) : D (a • z) = d a • z + a • D z := by sorry
