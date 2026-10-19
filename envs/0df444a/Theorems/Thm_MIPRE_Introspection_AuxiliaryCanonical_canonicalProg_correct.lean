-- Prove2me | Theorems.Thm_MIPRE_Introspection_AuxiliaryCanonical_canonicalProg_correct
-- name    : MIPRE.Introspection.AuxiliaryCanonical.canonicalProg_correct
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:49:05.613501+00:00
-- url     : https://prove2.me/theorems/7edfcd5d-5193-4b20-a957-6b7bfe27b863
-- title:
--   Lemma canonicalProg_correct of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.AuxiliaryCanonicalProgram` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Verified canonical binary elimination for auxiliary dual checks. The effective elimination library chooses the first nonzero coordinate at each insertion. Its resulting pivot set is exactly the dimension-defined canonical pivot set used by `CL.canonLin`. Thus its residual, not merely an arbitrary equivalent quotient representative, computes that canonical map.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Introspection.AuxiliaryCanonical
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.LowDegree.BinaryLinear
--   open Finset Submodule Module
--   variable {n t : ℕ}
--
--   theorem MIPRE.Introspection.AuxiliaryCanonical.canonicalProg_correct (vs : List (Fin n → ZMod 2)) (v : Fin n → ZMod 2) :
--       canonicalProg (vs.map vectorBits,vectorBits v) =
--         vectorBits (CL.canonLin (Submodule.span (ZMod 2) {x | x ∈ vs}) v)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.AuxiliaryCanonical.canonicalProg_correct` is declared in `MIPRE/Foundations/Introspection/AuxiliaryCanonicalProgram.lean`, lines 171–188. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AuxiliaryCanonicalProgram.lean#L171-L188; blueprint lem:intro-executable-padded-auxiliary

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

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.AuxiliaryCanonical
open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.LowDegree.BinaryLinear
open Finset Submodule Module
variable {n t : ℕ}

theorem MIPRE.Introspection.AuxiliaryCanonical.canonicalProg_correct (vs : List (Fin n → ZMod 2)) (v : Fin n → ZMod 2) :
    canonicalProg (vs.map vectorBits,vectorBits v) =
      vectorBits (CL.canonLin (Submodule.span (ZMod 2) {x | x ∈ vs}) v) := by sorry
