-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryLinear_typedReduceStep_error
-- name    : MIPRE.LowDegree.BinaryLinear.typedReduceStep_error
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:48:08.331848+00:00
-- url     : https://prove2.me/theorems/7619e03d-58d9-4df1-ab23-b0a5826e3eaa
-- title:
--   The vector plus the image of its certificate is unchanged by reduction
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinarySolve` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Solving binary linear systems with certified elimination
--
--   The vector plus the image of its certificate is unchanged by reduction.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryLinear
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun
--   variable {n t : ℕ}
--
--   theorem MIPRE.LowDegree.BinaryLinear.typedReduceStep_error
--       (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
--       (r : Row n t) (p : Pivot n t) (hp : Represents L p.2) :
--       (typedReduceStep r p).1 + L (typedReduceStep r p).2 = r.1 + L r.2
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryLinear.typedReduceStep_error` is declared in `MIPRE/Foundations/LowDegree/BinarySolve.lean`, lines 93–108. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinarySolve.lean#L93-L108

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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryLinear
open MIPRE.Cost MIPRE.Cost.PolyTimeFun
variable {n t : ℕ}

theorem MIPRE.LowDegree.BinaryLinear.typedReduceStep_error
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (r : Row n t) (p : Pivot n t) (hp : Represents L p.2) :
    (typedReduceStep r p).1 + L (typedReduceStep r p).2 = r.1 + L r.2 := by sorry
