-- Prove2me | Theorems.Thm_MIPRE_Pipeline_toUnaryProg_runs
-- name    : MIPRE.Pipeline.toUnaryProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:12:34.191593+00:00
-- url     : https://prove2.me/theorems/79877215-18bd-425b-aee3-6a29e6c820b6
-- title:
--   Lemma toUnaryProg_runs of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.Pipeline.UnaryArith` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Unary arithmetic by loops. The routines the pipeline's parameter computations need, whose running time is polynomial in the *value* of their input rather than its size: writing a binary number in unary (`toUnaryProg`) and raising a unary number to a binary power (`powProg`). Both are `whileProg` loops (`MIPRE/Foundations/Cost/While`) of polynomial-time steps.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Pipeline
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.CL.Detyping.Program MIPRE.LowDegree.DegreeArithmetic
--
--   theorem MIPRE.Pipeline.toUnaryProg_runs (x : ℕ) : ∃ t, toUnaryProg.Runs (encode x) (encode (unary x)) t
--   ```
--
--   **Formalization Note** `MIPRE.Pipeline.toUnaryProg_runs` is declared in `MIPRE/Foundations/Pipeline/UnaryArith.lean`, lines 65–76. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Pipeline/UnaryArith.lean#L65-L76

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_Cost_While
import Definitions.Def_MIPRE_Foundations_Pipeline_UnaryArith

open MIPRE
open MIPRE.Pipeline
open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.CL.Detyping.Program MIPRE.LowDegree.DegreeArithmetic

theorem MIPRE.Pipeline.toUnaryProg_runs (x : ℕ) : ∃ t, toUnaryProg.Runs (encode x) (encode (unary x)) t := by sorry
