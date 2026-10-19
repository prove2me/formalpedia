-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryPrimePowerTrace_traceElement_natDegree_of_root_degrees
-- name    : MIPRE.LowDegree.BinaryPrimePowerTrace.traceElement_natDegree_of_root_degrees
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:59:17.108724+00:00
-- url     : https://prove2.me/theorems/5b756a6a-fa05-4a01-b8c5-04e71e6d5d62
-- title:
--   The intermediate-field premises follow from the two exact root degrees
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryPrimePowerTrace` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Exact degree of the odd-prime Shoup trace
--
--   The intermediate-field premises follow from the two exact root degrees.
--   This form applies directly to the flat Kummer quotient.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryPrimePowerTrace
--   open Polynomial IntermediateField
--
--   theorem MIPRE.LowDegree.BinaryPrimePowerTrace.traceElement_natDegree_of_root_degrees {E : Type*} [Field E] [Finite E]
--       [Algebra (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
--       (β : E) (m q e : ℕ) (hm : 0 < m) (hq : q.Prime)
--       (horder : orderOf (2 : ZMod q) = m) (hcop : q.Coprime m)
--       (hprim : IntermediateField.adjoin (ZMod 2) ({β} : Set E) = ⊤)
--       (hβ : (minpoly (ZMod 2) β).natDegree = m * q ^ (e + 1))
--       (hβq : (minpoly (ZMod 2) (β ^ q)).natDegree = m * q ^ e) :
--       (minpoly (ZMod 2) (traceElement β m (q ^ (e + 1)))).natDegree = q ^ (e + 1)
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryPrimePowerTrace.traceElement_natDegree_of_root_degrees` is declared in `MIPRE/Foundations/LowDegree/BinaryPrimePowerTrace.lean`, lines 138–172. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryPrimePowerTrace.lean#L138-L172

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFactorization
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCyclotomicSeed
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySubstitution
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueCorrectness
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerTrace

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryPrimePowerTrace
open Polynomial IntermediateField

theorem MIPRE.LowDegree.BinaryPrimePowerTrace.traceElement_natDegree_of_root_degrees {E : Type*} [Field E] [Finite E]
    [Algebra (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (β : E) (m q e : ℕ) (hm : 0 < m) (hq : q.Prime)
    (horder : orderOf (2 : ZMod q) = m) (hcop : q.Coprime m)
    (hprim : IntermediateField.adjoin (ZMod 2) ({β} : Set E) = ⊤)
    (hβ : (minpoly (ZMod 2) β).natDegree = m * q ^ (e + 1))
    (hβq : (minpoly (ZMod 2) (β ^ q)).natDegree = m * q ^ e) :
    (minpoly (ZMod 2) (traceElement β m (q ^ (e + 1)))).natDegree = q ^ (e + 1) := by sorry
