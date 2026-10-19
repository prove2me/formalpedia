-- Prove2me | Theorems.Thm_MIPRE_Introspection_polynomial_ansBound
-- name    : MIPRE.Introspection.polynomial_ansBound
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:10:29.564225+00:00
-- url     : https://prove2.me/theorems/abe4cf39-64d6-4139-b7f5-1f3e776620eb
-- title:
--   Any fixed polynomial overhead is absorbed by another polynomial exponent
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.Runtime` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Absolute simulation bounds on the original legal answer cut. Ambient boundedness controls input-size degree as well as a time coefficient. On four bit strings of length at most `(2^n)^λ`, the resulting absolute cost has a quadratic exponent in `λ`. The polynomial-exponent introspection budget absorbs this cost without enlarging the original game's answer alphabet. These lemmas concern actual source and universal-simulator runs. They do not yet construct the introspective decider's format checks or other subtests.
--
--   Any fixed polynomial overhead is absorbed by another polynomial exponent.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Cost
--
--   theorem MIPRE.Introspection.polynomial_ansBound (P : Polynomial ℕ) (k : ℕ) :
--       ∃ C, ∀ lam n, 1 ≤ lam → 1 ≤ n →
--         P.eval (ansBound k lam n) ≤ ansBound C lam n
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.polynomial_ansBound` is declared in `MIPRE/Foundations/Introspection/Runtime.lean`, lines 77–94. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/Runtime.lean#L77-L94; blueprint lem:intro-ambient-runtime

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Introspection
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded

open MIPRE
open MIPRE.Introspection
open MIPRE.Cost

theorem MIPRE.Introspection.polynomial_ansBound (P : Polynomial ℕ) (k : ℕ) :
    ∃ C, ∀ lam n, 1 ≤ lam → 1 ≤ n →
      P.eval (ansBound k lam n) ≤ ansBound C lam n := by sorry
