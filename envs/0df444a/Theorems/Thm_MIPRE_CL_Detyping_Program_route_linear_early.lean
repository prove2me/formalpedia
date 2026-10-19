-- Prove2me | Theorems.Thm_MIPRE_CL_Detyping_Program_route_linear_early
-- name    : MIPRE.CL.Detyping.Program.route_linear_early
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:09:31.007502+00:00
-- url     : https://prove2.me/theorems/45519aba-bc97-4c9c-a79c-b64db94b4daa
-- title:
--   Lemma route_linear_early of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingProgBranches` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Correct query branches of the executable detyping router
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.Detyping
--   open MIPRE.CL.Detyping.Program
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun
--   variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
--   variable (E : T → T → Prop) [DecidableRel E]
--
--   theorem MIPRE.CL.Detyping.Program.route_linear_early (n : ℕ) (w : Player) (j : ℕ) (u y : BitStr)
--       (hj : 1 ≤ j) (hj' : j ≤ 2) :
--       route E (encode (n, Sampler.Query.linear w j u y)) =
--         directResult (graphBits ((Graph.presentation E w.toBool).mapOfPrefix (j - 1)
--           (graphOfBits u) (graphOfBits y)) ++ pad false (content (graphDim T) y))
--   ```
--
--   **Formalization Note** `MIPRE.CL.Detyping.Program.route_linear_early` is declared in `MIPRE/Foundations/CL/DetypingProgBranches.lean`, lines 43–49. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingProgBranches.lean#L43-L49

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
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
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute

open MIPRE
open MIPRE.CL
open MIPRE.CL.Detyping
open MIPRE.CL.Detyping.Program
open MIPRE.Cost MIPRE.Cost.PolyTimeFun
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable (E : T → T → Prop) [DecidableRel E]

theorem MIPRE.CL.Detyping.Program.route_linear_early (n : ℕ) (w : Player) (j : ℕ) (u y : BitStr)
    (hj : 1 ≤ j) (hj' : j ≤ 2) :
    route E (encode (n, Sampler.Query.linear w j u y)) =
      directResult (graphBits ((Graph.presentation E w.toBool).mapOfPrefix (j - 1)
        (graphOfBits u) (graphOfBits y)) ++ pad false (content (graphDim T) y)) := by sorry
