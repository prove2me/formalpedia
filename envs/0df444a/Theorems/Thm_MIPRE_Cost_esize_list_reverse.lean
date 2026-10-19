-- Prove2me | Theorems.Thm_MIPRE_Cost_esize_list_reverse
-- name    : MIPRE.Cost.esize_list_reverse
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:20:58.128613+00:00
-- url     : https://prove2.me/theorems/8ed277cd-8c01-4c86-8942-9580611da16e
-- title:
--   Lemma esize_list_reverse of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.Cost.Fold` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The closure library, part IV: folds over lists. The generic iteration combinator of the library, `PolyTimeFun.foldl`: a fold of a polynomial-time body over a list is polynomial-time provided the accumulator grows by at most an additive polynomial in the element at each step (the Cobham condition `esize (F (s, a)) ≤ esize s + B (esize a)`), and from it `cons`, `casesList`, `map`, `zip`, `append`, `replicate` and `reverse` (`planning/succinct-cook-levin.md`, S3). Every combinator's `toFun` is the corresponding `List` function, so that a program assembled from them is *defined* by its…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Cost
--   open Polynomial
--   variable {α : Type*} [SizedEncoding α]
--
--   theorem MIPRE.Cost.esize_list_reverse (l : List α) : esize l.reverse = esize l
--   ```
--
--   **Formalization Note** `MIPRE.Cost.esize_list_reverse` is declared in `MIPRE/Foundations/Cost/Fold.lean`, lines 70–76. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Fold.lean#L70-L76

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold

open MIPRE
open MIPRE.Cost
open Polynomial
variable {α : Type*} [SizedEncoding α]

theorem MIPRE.Cost.esize_list_reverse (l : List α) : esize l.reverse = esize l := by sorry
