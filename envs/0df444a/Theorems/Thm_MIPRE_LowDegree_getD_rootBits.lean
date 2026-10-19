-- Prove2me | Theorems.Thm_MIPRE_LowDegree_getD_rootBits
-- name    : MIPRE.LowDegree.getD_rootBits
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:12:12.523304+00:00
-- url     : https://prove2.me/theorems/7cc9c70c-4af7-420a-837b-36b5ab67d244
-- title:
--   Lemma getD_rootBits of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinarySquareRoot` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). A polynomial-time square root in the binary cyclic group algebra. For an odd-length coefficient vector, reading the doubled indices means reading the even positions followed by the odd positions. Splitting those two lists and appending them is polynomial-time in the ambient cost model. This implements the square-root step of self-dualization; it does not compute the inverse Gram element or the initial normal basis.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.Cost
--   variable {α : Type*}
--
--   theorem MIPRE.LowDegree.getD_rootBits (l : List α) (fallback : α) (hodd : Odd l.length)
--       {i : ℕ} (hi : i < l.length) :
--       (rootBits l).getD i fallback = l.getD ((i + i) % l.length) fallback
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.getD_rootBits` is declared in `MIPRE/Foundations/LowDegree/BinarySquareRoot.lean`, lines 69–87. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinarySquareRoot.lean#L69-L87

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySquareRoot

open MIPRE
open MIPRE.LowDegree
open MIPRE.Cost
variable {α : Type*}

theorem MIPRE.LowDegree.getD_rootBits (l : List α) (fallback : α) (hodd : Odd l.length)
    {i : ℕ} (hi : i < l.length) :
    (rootBits l).getD i fallback = l.getD ((i + i) % l.length) fallback := by sorry
