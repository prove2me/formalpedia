-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_halts
-- name    : MIPRE.Cost.Prog.routeOneCall_halts
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:10:31.866854+00:00
-- url     : https://prove2.me/theorems/08ef9bb1-624b-4f83-815c-a2786e434ae5
-- title:
--   Halting is preserved if each routed call retains the original index
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingProgCall` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). A total query router with at most one sampler call. The preprocessing program either supplies a direct result, or an argument and continuation context. Only the latter branch calls the supplied sampler. The postprocessor is total on raw data, so malformed inputs preserve termination whenever routing preserves the sampler index.
--
--   Halting is preserved if each routed call retains the original index.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Cost
--   open MIPRE.Cost.Prog
--   open MIPRE.Cost.PolyTimeFun
--
--   theorem MIPRE.Cost.Prog.routeOneCall_halts (route : PolyTimeFun Data (Bool × Data))
--       {p : Prog} (hp : p.WellScoped 1) (post : PolyTimeFun (Data × Data) Data)
--       (n : ℕ) (q : Data)
--       (halts : ∀ d, Halts p (.cons (encode n) d))
--       (preserves : ∀ a, route (.cons (encode n) q) = (true, a) →
--         ∃ d ctx, a = .cons (.cons (encode n) d) ctx) :
--       Halts (routeOneCall route p post) (.cons (encode n) q)
--   ```
--
--   **Formalization Note** `MIPRE.Cost.Prog.routeOneCall_halts` is declared in `MIPRE/Foundations/CL/DetypingProgCall.lean`, lines 77–95. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingProgCall.lean#L77-L95

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

theorem MIPRE.Cost.Prog.routeOneCall_halts (route : PolyTimeFun Data (Bool × Data))
    {p : Prog} (hp : p.WellScoped 1) (post : PolyTimeFun (Data × Data) Data)
    (n : ℕ) (q : Data)
    (halts : ∀ d, Halts p (.cons (encode n) d))
    (preserves : ∀ a, route (.cons (encode n) q) = (true, a) →
      ∃ d ctx, a = .cons (.cons (encode n) d) ctx) :
    Halts (routeOneCall route p post) (.cons (encode n) q) := by sorry
