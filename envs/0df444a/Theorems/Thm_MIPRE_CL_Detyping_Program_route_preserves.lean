-- Prove2me | Theorems.Thm_MIPRE_CL_Detyping_Program_route_preserves
-- name    : MIPRE.CL.Detyping.Program.route_preserves
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:10:41.480277+00:00
-- url     : https://prove2.me/theorems/f886963c-5ea4-468f-ba6e-a40ef9023435
-- title:
--   Lemma route_preserves of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingProgRoute` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Executable routing of detyped queries. The fixed finite graph is compiled into a table. The variable content is processed by list operations and at most one call to the original typed sampler. Padding follows the supplied content vector, so malformed queries never cause an unbounded dimension allocation.
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
--
--   theorem MIPRE.CL.Detyping.Program.route_preserves (E : T → T → Prop) [DecidableRel E] (n : ℕ) (q payload : Data)
--       (h : route E (.cons (encode n) q) = (true, payload)) :
--       ∃ d ctx, payload = .cons (.cons (encode n) d) ctx
--   ```
--
--   **Formalization Note** `MIPRE.CL.Detyping.Program.route_preserves` is declared in `MIPRE/Foundations/CL/DetypingProgRoute.lean`, lines 176–180. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingProgRoute.lean#L176-L180

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

theorem MIPRE.CL.Detyping.Program.route_preserves (E : T → T → Prop) [DecidableRel E] (n : ℕ) (q payload : Data)
    (h : route E (.cons (encode n) q) = (true, payload)) :
    ∃ d ctx, payload = .cons (.cons (encode n) d) ctx := by sorry
