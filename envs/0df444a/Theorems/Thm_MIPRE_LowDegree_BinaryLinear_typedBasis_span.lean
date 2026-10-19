-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryLinear_typedBasis_span
-- name    : MIPRE.LowDegree.BinaryLinear.typedBasis_span
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:11:48.09538+00:00
-- url     : https://prove2.me/theorems/5108e465-8930-43ee-baf7-ba8e6df233ce
-- title:
--   The constructed independent vectors span the original family
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryBasis` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Correctness of the effective binary basis construction
--
--   The constructed independent vectors span the original family.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryLinear
--   variable {n t : ℕ}
--
--   theorem MIPRE.LowDegree.BinaryLinear.typedBasis_span (rows : List (Row n t)) : pivotSpan (typedBasis rows) = rowSpan rows
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryLinear.typedBasis_span` is declared in `MIPRE/Foundations/LowDegree/BinaryBasis.lean`, lines 173–185. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryBasis.lean#L173-L185; blueprint lem:effective-binary-linear-algebra

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryLinear
variable {n t : ℕ}

theorem MIPRE.LowDegree.BinaryLinear.typedBasis_span (rows : List (Row n t)) : pivotSpan (typedBasis rows) = rowSpan rows := by sorry
