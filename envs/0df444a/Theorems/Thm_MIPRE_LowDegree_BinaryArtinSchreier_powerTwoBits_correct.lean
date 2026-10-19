-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryArtinSchreier_powerTwoBits_correct
-- name    : MIPRE.LowDegree.BinaryArtinSchreier.powerTwoBits_correct
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T03:36:14.023593+00:00
-- url     : https://prove2.me/theorems/b5ce1ceb-6549-4eb5-832a-fc5390a07444
-- title:
--   The globally polynomial-time program constructs a monic irreducible binary polynomial of every requested power-of-two degree, including degree one
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryArtinSchreierLoop` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The bounded power-of-two constructor. The input is the requested degree in unary. The loop caps all intermediate moduli by this input degree, including on malformed states. The unbounded mathematical stage sequence below is used only to state the induction proof.
--
--   The globally polynomial-time program constructs a monic irreducible binary
--   polynomial of every requested power-of-two degree, including degree one.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryArtinSchreier
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.LowDegree.BinaryPolynomial Polynomial
--
--   theorem MIPRE.LowDegree.BinaryArtinSchreier.powerTwoBits_correct (e : ℕ) :
--       (polyOfBits (powerTwoBits (unary (2 ^ e)))).Monic ∧
--         Irreducible (polyOfBits (powerTwoBits (unary (2 ^ e)))) ∧
--         (polyOfBits (powerTwoBits (unary (2 ^ e)))).natDegree = 2 ^ e
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryArtinSchreier.powerTwoBits_correct` is declared in `MIPRE/Foundations/LowDegree/BinaryArtinSchreierLoop.lean`, lines 187–204. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryArtinSchreierLoop.lean#L187-L204; blueprint lem:binary-power-two-irreducible

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Content
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierTower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierLoop

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryArtinSchreier
open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.LowDegree.BinaryPolynomial Polynomial

theorem MIPRE.LowDegree.BinaryArtinSchreier.powerTwoBits_correct (e : ℕ) :
    (polyOfBits (powerTwoBits (unary (2 ^ e)))).Monic ∧
      Irreducible (polyOfBits (powerTwoBits (unary (2 ^ e)))) ∧
      (polyOfBits (powerTwoBits (unary (2 ^ e)))).natDegree = 2 ^ e := by sorry
