-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_composedSumBits_correct
-- name    : MIPRE.LowDegree.BinaryQuotient.composedSumBits_correct
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:56:27.298134+00:00
-- url     : https://prove2.me/theorems/76c5d8b7-2bbf-4629-9bf0-6d84d90c1f48
-- title:
--   The uniform composed-sum program combines irreducible polynomials of coprime degrees
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryComposedSum` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Correctness of the effective coprime-degree composed-sum construction
--
--   The uniform composed-sum program combines irreducible polynomials of coprime degrees.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryQuotient
--   open MIPRE.Cost MIPRE.LowDegree.BinaryPolynomial Polynomial MIPRE.LowDegree.BinaryFiniteField
--   variable (f : Polynomial (ZMod 2)) (hf : f.Monic) [Fact (Irreducible f)]
--
--   theorem MIPRE.LowDegree.BinaryQuotient.composedSumBits_correct (p g : BitStr) (hp : p.length = f.natDegree)
--       (hpoly : f = polyOfBits (p ++ [true])) (hg : (polyOfBits g).Monic)
--       (hgi : Irreducible (polyOfBits g)) (hcop : f.natDegree.Coprime (polyOfBits g).natDegree) :
--       (polyOfBits (composedSumBits p g)).Monic ∧ Irreducible (polyOfBits (composedSumBits p g)) ∧
--         (polyOfBits (composedSumBits p g)).natDegree = f.natDegree * (polyOfBits g).natDegree
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryQuotient.composedSumBits_correct` is declared in `MIPRE/Foundations/LowDegree/BinaryComposedSum.lean`, lines 83–117. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryComposedSum.lean#L83-L117; blueprint lem:binary-coprime-degree-combination

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
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientTranslation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumProg

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryQuotient
open MIPRE.Cost MIPRE.LowDegree.BinaryPolynomial Polynomial MIPRE.LowDegree.BinaryFiniteField
variable (f : Polynomial (ZMod 2)) (hf : f.Monic) [Fact (Irreducible f)]
include hf

theorem MIPRE.LowDegree.BinaryQuotient.composedSumBits_correct (p g : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hg : (polyOfBits g).Monic)
    (hgi : Irreducible (polyOfBits g)) (hcop : f.natDegree.Coprime (polyOfBits g).natDegree) :
    (polyOfBits (composedSumBits p g)).Monic ∧ Irreducible (polyOfBits (composedSumBits p g)) ∧
      (polyOfBits (composedSumBits p g)).natDegree = f.natDegree * (polyOfBits g).natDegree := by sorry
