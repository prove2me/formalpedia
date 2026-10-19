-- Prove2me | Theorems.Thm_MIPRE_LowDegree_DegreeArithmetic_ascendingUnary_eq
-- name    : MIPRE.LowDegree.DegreeArithmetic.ascendingUnary_eq
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:11:38.234524+00:00
-- url     : https://prove2.me/theorems/6a9d63d8-6975-4663-975f-58d1ae1313d6
-- title:
--   The enumeration is the bounded canonical unary list from zero to the input
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryDegreeDecomposition` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Executable prime-power decomposition of a unary requested degree
--
--   The enumeration is the bounded canonical unary list from zero to the input.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.DegreeArithmetic
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun
--
--   theorem MIPRE.LowDegree.DegreeArithmetic.ascendingUnary_eq (u : Unary) :
--       ascendingUnary u = List.ofFn (fun i : Fin (u.length + 1) => unary (i : ℕ))
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.DegreeArithmetic.ascendingUnary_eq` is declared in `MIPRE/Foundations/LowDegree/BinaryDegreeDecomposition.lean`, lines 23–39. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryDegreeDecomposition.lean#L23-L39

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimality
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimePower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeDecomposition

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.DegreeArithmetic
open MIPRE.Cost MIPRE.Cost.PolyTimeFun

theorem MIPRE.LowDegree.DegreeArithmetic.ascendingUnary_eq (u : Unary) :
    ascendingUnary u = List.ofFn (fun i : Fin (u.length + 1) => unary (i : ℕ)) := by sorry
