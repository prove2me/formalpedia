-- Prove2me | Theorems.Thm_MIPRE_LowDegree_DegreeArithmetic_rawPrimePower_correct
-- name    : MIPRE.LowDegree.DegreeArithmetic.rawPrimePower_correct
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:12:23.320153+00:00
-- url     : https://prove2.me/theorems/35d6cc7e-ef2c-4d83-91e7-27c8636ef9d6
-- title:
--   Unary input length supplies enough iterations to reach the maximal prime-power divisor
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.UnaryPrimePower` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # A capped unary program for maximal prime-power divisors
--
--   Unary input length supplies enough iterations to reach the maximal prime-power divisor.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.DegreeArithmetic
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial
--
--   theorem MIPRE.LowDegree.DegreeArithmetic.rawPrimePower_correct (n q : ℕ) (hq : q.Prime) :
--       rawPrimePower (unary n) (unary q) = unary (q ^ n.factorization q)
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.DegreeArithmetic.rawPrimePower_correct` is declared in `MIPRE/Foundations/LowDegree/UnaryPrimePower.lean`, lines 114–127. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/UnaryPrimePower.lean#L114-L127

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
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

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.DegreeArithmetic
open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial

theorem MIPRE.LowDegree.DegreeArithmetic.rawPrimePower_correct (n q : ℕ) (hq : q.Prime) :
    rawPrimePower (unary n) (unary q) = unary (q ^ n.factorization q) := by sorry
