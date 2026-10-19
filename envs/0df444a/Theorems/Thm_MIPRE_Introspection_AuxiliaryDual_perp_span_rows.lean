-- Prove2me | Theorems.Thm_MIPRE_Introspection_AuxiliaryDual_perp_span_rows
-- name    : MIPRE.Introspection.AuxiliaryDual.perp_span_rows
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:50:13.757086+00:00
-- url     : https://prove2.me/theorems/d75af45e-50ca-4548-ab65-cc037313adae
-- title:
--   Orthogonality to all matrix rows is precisely the kernel condition
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.AuxiliaryDualProgram` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Executable canonical dual of a binary linear map. The rows of a matrix span the dot-product orthogonal complement of its kernel. Canonical elimination of those rows therefore computes the exact `CL.lperp`, including for singular matrices and in dimension zero.
--
--   Orthogonality to all matrix rows is precisely the kernel condition.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Introspection.AuxiliaryDual
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.LowDegree.BinaryLinear
--   variable {F : Type*} [Field F] {m n : ℕ}
--
--   theorem MIPRE.Introspection.AuxiliaryDual.perp_span_rows (A : Matrix (Fin m) (Fin n) F) :
--       CL.perp (Submodule.span F (Set.range A)) = A.mulVecLin.ker
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.AuxiliaryDual.perp_span_rows` is declared in `MIPRE/Foundations/Introspection/AuxiliaryDualProgram.lean`, lines 33–51. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AuxiliaryDualProgram.lean#L33-L51

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
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryCanonicalProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualProgram

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.AuxiliaryDual
open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.LowDegree.BinaryLinear
set_option backward.isDefEq.respectTransparency false
variable {F : Type*} [Field F] {m n : ℕ}

theorem MIPRE.Introspection.AuxiliaryDual.perp_span_rows (A : Matrix (Fin m) (Fin n) F) :
    CL.perp (Submodule.span F (Set.range A)) = A.mulVecLin.ker := by sorry
