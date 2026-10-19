-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_orbitPolynomialBits_monic_natDegree
-- name    : MIPRE.LowDegree.BinaryQuotient.orbitPolynomialBits_monic_natDegree
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:36:00.829612+00:00
-- url     : https://prove2.me/theorems/9a452174-aaf3-4bc9-b3d6-976b28c8f8a2
-- title:
--   The descended orbit product is monic and has the requested orbit degree
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryOrbitDescent` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Descending a closed orbit product to binary coefficient bits
--
--   The descended orbit product is monic and has the requested orbit degree.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryQuotient
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.LowDegree.BinaryPolynomial Polynomial
--   variable {R : Type*} [CommRing R]
--   variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
--
--   theorem MIPRE.LowDegree.BinaryQuotient.orbitPolynomialBits_monic_natDegree [Fact (Irreducible f)]
--       (u : Unary) (p a : BitStr) (hp : p.length = f.natDegree)
--       (hpoly : f = polyOfBits (p ++ [true])) (hp0 : p ≠ []) (ha : a.length = p.length)
--       (hclosed : evalBits (AdjoinRoot.root f) a ^ (2 ^ u.length) =
--         evalBits (AdjoinRoot.root f) a) :
--       (polyOfBits (orbitPolynomialBits u p a)).Monic ∧
--         (polyOfBits (orbitPolynomialBits u p a)).natDegree = u.length
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryQuotient.orbitPolynomialBits_monic_natDegree` is declared in `MIPRE/Foundations/LowDegree/BinaryOrbitDescent.lean`, lines 108–123. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryOrbitDescent.lean#L108-L123; blueprint lem:binary-orbit-polynomial

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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryQuotient
open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.LowDegree.BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
include hf

theorem MIPRE.LowDegree.BinaryQuotient.orbitPolynomialBits_monic_natDegree [Fact (Irreducible f)]
    (u : Unary) (p a : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hp0 : p ≠ []) (ha : a.length = p.length)
    (hclosed : evalBits (AdjoinRoot.root f) a ^ (2 ^ u.length) =
      evalBits (AdjoinRoot.root f) a) :
    (polyOfBits (orbitPolynomialBits u p a)).Monic ∧
      (polyOfBits (orbitPolynomialBits u p a)).natDegree = u.length := by sorry
