-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_factorBitsProg_factors
-- name    : MIPRE.LowDegree.BinaryQuotient.factorBitsProg_factors
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:55:42.879905+00:00
-- url     : https://prove2.me/theorems/6f261c30-ba61-472d-be56-fb919212abf0
-- title:
--   Every output of squarefree binary factorization is monic and irreducible
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryFactorization` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Deterministic squarefree factorization over the binary field. Frobenius fixed-space separation computes primitive idempotents of the monic quotient. The factor supported by an idempotent represented by `E` is `gcd(f, E - 1)`. All executing operations are uniform ambient programs; the finite-ring arguments justify correctness without enumerating the quotient.
--
--   Every output of squarefree binary factorization is monic and irreducible.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryQuotient
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial MIPRE.LowDegree.BinaryPolynomial
--   variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
--
--   theorem MIPRE.LowDegree.BinaryQuotient.factorBitsProg_factors (p : BitStr) (hp : p.length = f.natDegree)
--       (hpoly : f = polyOfBits (p ++ [true])) (hp0 : p ≠ []) (hs : Squarefree f) :
--       ∀ a ∈ factorBitsProg p, (polyOfBits a).Monic ∧ Irreducible (polyOfBits a)
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryQuotient.factorBitsProg_factors` is declared in `MIPRE/Foundations/LowDegree/BinaryFactorization.lean`, lines 65–85. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryFactorization.lean#L65-L85; blueprint lem:binary-squarefree-factorization

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
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
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

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryQuotient
open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial MIPRE.LowDegree.BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
include hf

theorem MIPRE.LowDegree.BinaryQuotient.factorBitsProg_factors (p : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hp0 : p ≠ []) (hs : Squarefree f) :
    ∀ a ∈ factorBitsProg p, (polyOfBits a).Monic ∧ Irreducible (polyOfBits a) := by sorry
