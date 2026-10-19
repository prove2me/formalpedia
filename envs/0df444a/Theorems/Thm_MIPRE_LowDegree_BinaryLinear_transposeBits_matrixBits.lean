-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryLinear_transposeBits_matrixBits
-- name    : MIPRE.LowDegree.BinaryLinear.transposeBits_matrixBits
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:11:45.633464+00:00
-- url     : https://prove2.me/theorems/f930f188-f6ea-460c-a757-c7926b42a411
-- title:
--   Raw transposition agrees with typed matrix transposition
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryLinear` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Executable binary vector and matrix arithmetic
--
--   Raw transposition agrees with typed matrix transposition.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryLinear
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun
--
--   theorem MIPRE.LowDegree.BinaryLinear.transposeBits_matrixBits {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
--       transposeBits n (matrixBits A) = matrixBits A.transpose
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryLinear.transposeBits_matrixBits` is declared in `MIPRE/Foundations/LowDegree/BinaryLinear.lean`, lines 131–144. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryLinear.lean#L131-L144; blueprint lem:effective-binary-linear-algebra

import Mathlib.Algebra.CharP.Two
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

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryLinear
open MIPRE.Cost MIPRE.Cost.PolyTimeFun

theorem MIPRE.LowDegree.BinaryLinear.transposeBits_matrixBits {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    transposeBits n (matrixBits A) = matrixBits A.transpose := by sorry
