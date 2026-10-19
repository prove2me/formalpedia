-- Prove2me | Theorems.Thm_MIPRE_LowDegree_ComponentFamily_linearIndependent
-- name    : MIPRE.LowDegree.ComponentFamily.linearIndependent
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:12:19.694985+00:00
-- url     : https://prove2.me/theorems/e9503138-32ef-4f8c-ba68-5d0f71af888b
-- title:
--   Nonzero orthogonal idempotents are linearly independent over the binary base field
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.IdempotentSplit` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Deterministic refinement by binary idempotents
--
--   Nonzero orthogonal idempotents are linearly independent over the binary base field.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   variable {R : Type*} [CommRing R] [DecidableEq R]
--   variable [Algebra (ZMod 2) R]
--
--   theorem MIPRE.LowDegree.ComponentFamily.linearIndependent {l : List R} (hl : ComponentFamily l) :
--       LinearIndependent (ZMod 2) (fun i : Fin l.length => l.get i)
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.ComponentFamily.linearIndependent` is declared in `MIPRE/Foundations/LowDegree/IdempotentSplit.lean`, lines 196–214. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/IdempotentSplit.lean#L196-L214

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit

open MIPRE
open MIPRE.LowDegree
variable {R : Type*} [CommRing R] [DecidableEq R]
variable [Algebra (ZMod 2) R]
attribute [local instance] MIPRE.LowDegree.instFactPrimeOfNatNat_mIPRE

theorem MIPRE.LowDegree.ComponentFamily.linearIndependent {l : List R} (hl : ComponentFamily l) :
    LinearIndependent (ZMod 2) (fun i : Fin l.length => l.get i) := by sorry
