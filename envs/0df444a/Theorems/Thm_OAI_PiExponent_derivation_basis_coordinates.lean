-- Prove2me | Theorems.Thm_OAI_PiExponent_derivation_basis_coordinates
-- name    : OAI.PiExponent.derivation_basis_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:27:08.443439+00:00
-- url     : https://prove2.me/theorems/6d232be1-576d-4feb-9d6c-e9a3a9037896
-- title:
--   Coordinates of a derivation in a finite field-extension basis
-- statement:
--   Let $k\subseteq F\subseteq E$ be a compatible field tower with compatible $k$-derivations $d$ on $F$ and $D$ on $E$. For a finite $F$-basis $(b_j)$ of $E$, an element $z=\sum_j z_jb_j$, and every index $i$,
--   $$[D(z)]_i=d(z_i)+\sum_j z_j[D(b_j)]_i.$$
--   The formula records both differentiation of the coordinates and variation of the basis.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LogarithmicObstruction.lean#L111-L124

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

theorem OAI.PiExponent.derivation_basis_coordinates
    {k F E ι : Type*} [Field k] [Field F] [Field E] [Fintype ι]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    (d : Derivation k F F) (D : Derivation k E E)
    (hcompat : ∀ a : F, D (algebraMap F E a) = algebraMap F E (d a))
    (b : Module.Basis ι F E) (z : E) (i : ι) :
    b.repr (D z) i = d (b.repr z i) +
      ∑ j, b.repr z j * b.repr (D (b j)) i := by sorry
