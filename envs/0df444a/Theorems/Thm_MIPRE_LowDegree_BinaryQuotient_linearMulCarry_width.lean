-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_linearMulCarry_width
-- name    : MIPRE.LowDegree.BinaryQuotient.linearMulCarry_width
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:36:21.164459+00:00
-- url     : https://prove2.me/theorems/dd3d4d53-1fc2-4c50-a99c-3c5ed096e0b7
-- title:
--   The carried linear multiplication preserves correct coefficient widths
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryQuotientOrbit` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Polynomial products with coefficients in an explicit binary quotient
--
--   The carried linear multiplication preserves correct coefficient widths.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryQuotient
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.LowDegree.BinaryPolynomial Polynomial
--   variable {R : Type*} [CommRing R]
--
--   theorem MIPRE.LowDegree.BinaryQuotient.linearMulCarry_width (p a carry : BitStr) (cs : List BitStr)
--       (ha : a.length = p.length) (hc : carry.length = p.length)
--       (hs : ∀ c ∈ cs, c.length = p.length) :
--       ∀ c ∈ linearMulCarry p a carry cs, c.length = p.length
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryQuotient.linearMulCarry_width` is declared in `MIPRE/Foundations/LowDegree/BinaryQuotientOrbit.lean`, lines 44–64. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryQuotientOrbit.lean#L44-L64

import Mathlib.Algebra.CharP.Algebra
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
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryQuotient
open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.LowDegree.BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]

theorem MIPRE.LowDegree.BinaryQuotient.linearMulCarry_width (p a carry : BitStr) (cs : List BitStr)
    (ha : a.length = p.length) (hc : carry.length = p.length)
    (hs : ∀ c ∈ cs, c.length = p.length) :
    ∀ c ∈ linearMulCarry p a carry cs, c.length = p.length := by sorry
