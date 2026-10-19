-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_componentFactor_dvd_iff
-- name    : MIPRE.LowDegree.BinaryQuotient.componentFactor_dvd_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:11:36.730791+00:00
-- url     : https://prove2.me/theorems/17db8a44-f09d-42c5-8d03-faaf484df0de
-- title:
--   An idempotent's supported factor describes its polynomial annihilator
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryQuotientFactors` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Extracting polynomial factors from primitive quotient components. An idempotent represented by `E` corresponds to the factor `gcd(f,E-1)`. Its multiples are exactly the polynomials annihilated by that component. Primitive-component inverses therefore prove irreducibility without a Chinese remainder construction or an enumeration of the quotient ring.
--
--   An idempotent's supported factor describes its polynomial annihilator.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryQuotient
--   open Polynomial
--
--   theorem MIPRE.LowDegree.BinaryQuotient.componentFactor_dvd_iff (f E H : Polynomial (ZMod 2))
--       (he : AdjoinRoot.mk f E * AdjoinRoot.mk f E = AdjoinRoot.mk f E) :
--       componentFactor f E ∣ H ↔ AdjoinRoot.mk f E * AdjoinRoot.mk f H = 0
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryQuotient.componentFactor_dvd_iff` is declared in `MIPRE/Foundations/LowDegree/BinaryQuotientFactors.lean`, lines 30–49. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryQuotientFactors.lean#L30-L49

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

theorem MIPRE.LowDegree.BinaryQuotient.componentFactor_dvd_iff (f E H : Polynomial (ZMod 2))
    (he : AdjoinRoot.mk f E * AdjoinRoot.mk f E = AdjoinRoot.mk f E) :
    componentFactor f E ∣ H ↔ AdjoinRoot.mk f E * AdjoinRoot.mk f H = 0 := by sorry
