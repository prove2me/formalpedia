-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_closed
-- name    : MIPRE.Cost.Prog.routeOneCall_closed
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:10:16.898986+00:00
-- url     : https://prove2.me/theorems/3a7bfd7a-7a0b-4716-931b-3cbb41355513
-- title:
--   Lemma routeOneCall_closed of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingProgCall` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). A total query router with at most one sampler call. The preprocessing program either supplies a direct result, or an argument and continuation context. Only the latter branch calls the supplied sampler. The postprocessor is total on raw data, so malformed inputs preserve termination whenever routing preserves the sampler index.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Cost
--   open MIPRE.Cost.Prog
--   open MIPRE.Cost.PolyTimeFun
--
--   theorem MIPRE.Cost.Prog.routeOneCall_closed (route : PolyTimeFun Data (Bool × Data))
--       {p : Prog} (hp : p.WellScoped 1) (post : PolyTimeFun (Data × Data) Data) :
--       (routeOneCall route p post).WellScoped 1
--   ```
--
--   **Formalization Note** `MIPRE.Cost.Prog.routeOneCall_closed` is declared in `MIPRE/Foundations/CL/DetypingProgCall.lean`, lines 48–52. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingProgCall.lean#L48-L52

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
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
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open MIPRE.Cost.PolyTimeFun

theorem MIPRE.Cost.Prog.routeOneCall_closed (route : PolyTimeFun Data (Bool × Data))
    {p : Prog} (hp : p.WellScoped 1) (post : PolyTimeFun (Data × Data) Data) :
    (routeOneCall route p post).WellScoped 1 := by sorry
