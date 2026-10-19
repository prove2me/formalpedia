-- Prove2me | Theorems.Thm_MIPRE_Introspection_SourceDescriptionCompiler_exists_compiler_size
-- name    : MIPRE.Introspection.SourceDescriptionCompiler.exists_compiler_size
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:10:36.692985+00:00
-- url     : https://prove2.me/theorems/87505c0e-aa10-4b80-9dea-cd0a436b02db
-- title:
--   A single constant absorbs the compiler's coefficient sum and degree
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.SourceDescriptionCompiler` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Uniformly bounded source descriptions for polynomial-time compilers. The compiler accepts arbitrary source descriptions. Each description exceeding the supplied binary parameter is replaced by a fixed program before compilation. This leaves every bounded verifier unchanged and gives a uniform polynomial output-size bound in the parameter, including at zero.
--
--   A single constant absorbs the compiler's coefficient sum and degree.
--   There is no lower-bound assumption on the supplied parameter.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Introspection.SourceDescriptionCompiler
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial
--   variable {β : Type*} [SizedEncoding β]
--
--   theorem MIPRE.Introspection.SourceDescriptionCompiler.exists_compiler_size (F : PolyTimeFun Input β) :
--       ∃ C : ℕ, 1 ≤ C ∧ ∀ (S D : Prog) (lam : ℕ),
--         esize (compiler F ((S, D), lam)) ≤ C * (lam + 1) ^ C
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.SourceDescriptionCompiler.exists_compiler_size` is declared in `MIPRE/Foundations/Introspection/SourceDescriptionCompiler.lean`, lines 90–107. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/SourceDescriptionCompiler.lean#L90-L107

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
import Mathlib.Tactic.Ring
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
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_SizeProgram
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Introspection_SourceDescriptionCompiler

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.SourceDescriptionCompiler
open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial
variable {β : Type*} [SizedEncoding β]

theorem MIPRE.Introspection.SourceDescriptionCompiler.exists_compiler_size (F : PolyTimeFun Input β) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (S D : Prog) (lam : ℕ),
      esize (compiler F ((S, D), lam)) ≤ C * (lam + 1) ^ C := by sorry
