-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_componentFactors_prod
-- name    : MIPRE.LowDegree.BinaryQuotient.componentFactors_prod
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:12:19.270026+00:00
-- url     : https://prove2.me/theorems/c5813df5-3f00-4d02-9cbd-5a6ee152674e
-- title:
--   A complete orthogonal primitive family reconstructs its monic quotient modulus
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryQuotientFactors` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Extracting polynomial factors from primitive quotient components. An idempotent represented by `E` corresponds to the factor `gcd(f,E-1)`. Its multiples are exactly the polynomials annihilated by that component. Primitive-component inverses therefore prove irreducibility without a Chinese remainder construction or an enumeration of the quotient ring.
--
--   A complete orthogonal primitive family reconstructs its monic quotient modulus.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryQuotient
--   open Polynomial
--
--   theorem MIPRE.LowDegree.BinaryQuotient.componentFactors_prod (f : Polynomial (ZMod 2)) (hf : f.Monic)
--       [Finite (AdjoinRoot f)]
--       (hsq : Function.Bijective (fun x : AdjoinRoot f => x * x))
--       {n : ℕ} (E : Fin n → Polynomial (ZMod 2))
--       (he : ∀ i, PrimitiveBinaryComponent (AdjoinRoot.mk f (E i)))
--       (horth : Pairwise (fun i j => AdjoinRoot.mk f (E i) * AdjoinRoot.mk f (E j) = 0))
--       (hsum : ∑ i, AdjoinRoot.mk f (E i) = 1) :
--       ∏ i, componentFactor f (E i) = f
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryQuotient.componentFactors_prod` is declared in `MIPRE/Foundations/LowDegree/BinaryQuotientFactors.lean`, lines 116–145. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryQuotientFactors.lean#L116-L145

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFactors

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryQuotient
open Polynomial

theorem MIPRE.LowDegree.BinaryQuotient.componentFactors_prod (f : Polynomial (ZMod 2)) (hf : f.Monic)
    [Finite (AdjoinRoot f)]
    (hsq : Function.Bijective (fun x : AdjoinRoot f => x * x))
    {n : ℕ} (E : Fin n → Polynomial (ZMod 2))
    (he : ∀ i, PrimitiveBinaryComponent (AdjoinRoot.mk f (E i)))
    (horth : Pairwise (fun i j => AdjoinRoot.mk f (E i) * AdjoinRoot.mk f (E j) = 0))
    (hsum : ∑ i, AdjoinRoot.mk f (E i) = 1) :
    ∏ i, componentFactor f (E i) = f := by sorry
