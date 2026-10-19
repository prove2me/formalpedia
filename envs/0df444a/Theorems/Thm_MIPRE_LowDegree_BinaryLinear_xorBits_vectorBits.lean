-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryLinear_xorBits_vectorBits
-- name    : MIPRE.LowDegree.BinaryLinear.xorBits_vectorBits
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:11:39.303986+00:00
-- url     : https://prove2.me/theorems/d99d7bd1-faf4-447a-997a-dfed00ba7689
-- title:
--   Coordinatewise XOR computes binary vector addition
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryLinear` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Executable binary vector and matrix arithmetic
--
--   Coordinatewise XOR computes binary vector addition.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryLinear
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun
--
--   theorem MIPRE.LowDegree.BinaryLinear.xorBits_vectorBits {n : ℕ} (v w : Fin n → ZMod 2) :
--       BinaryPolynomial.xorBits (vectorBits v) (vectorBits w) = vectorBits (v + w)
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryLinear.xorBits_vectorBits` is declared in `MIPRE/Foundations/LowDegree/BinaryLinear.lean`, lines 117–125. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryLinear.lean#L117-L125; blueprint lem:effective-binary-linear-algebra

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

theorem MIPRE.LowDegree.BinaryLinear.xorBits_vectorBits {n : ℕ} (v w : Fin n → ZMod 2) :
    BinaryPolynomial.xorBits (vectorBits v) (vectorBits w) = vectorBits (v + w) := by sorry
