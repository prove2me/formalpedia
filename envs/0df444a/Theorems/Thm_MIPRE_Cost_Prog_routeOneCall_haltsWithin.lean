-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_haltsWithin
-- name    : MIPRE.Cost.Prog.routeOneCall_haltsWithin
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:35:08.26793+00:00
-- url     : https://prove2.me/theorems/b12eaa67-0673-4e51-9d56-3058f76d0854
-- title:
--   Lemma routeOneCall_haltsWithin of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingProgCost` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Polynomial runtime transfer for the detyping sampler. The bound follows the actual one-call program: preprocessing bounds the size of the forwarded query and continuation, the original sampler bounds the forwarded run, and postprocessing reads their combined output. Constants in the graph table are fixed; no uniform graph-compilation bound is asserted.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Cost
--   open MIPRE.Cost.Prog
--   open MIPRE.Cost.PolyTimeFun Polynomial
--
--   theorem MIPRE.Cost.Prog.routeOneCall_haltsWithin (route : PolyTimeFun Data (Bool × Data))
--       {p : Prog} (hp : p.WellScoped 1) (post : PolyTimeFun (Data × Data) Data)
--       (n B k : ℕ) (q : Data)
--       (bound : ∀ d, HaltsWithin p (.cons (encode n) d) (B * (d.size + 1) ^ k))
--       (preserves : ∀ a, route (.cons (encode n) q) = (true, a) →
--         ∃ d ctx, a = .cons (.cons (encode n) d) ctx) :
--       HaltsWithin (routeOneCall route p post) (.cons (encode n) q)
--         ((routeCost route post B k).eval (Data.cons (encode n) q).size)
--   ```
--
--   **Formalization Note** `MIPRE.Cost.Prog.routeOneCall_haltsWithin` is declared in `MIPRE/Foundations/CL/DetypingProgCost.lean`, lines 111–162. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingProgCost.lean#L111-L162

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
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
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open MIPRE.Cost.PolyTimeFun Polynomial

theorem MIPRE.Cost.Prog.routeOneCall_haltsWithin (route : PolyTimeFun Data (Bool × Data))
    {p : Prog} (hp : p.WellScoped 1) (post : PolyTimeFun (Data × Data) Data)
    (n B k : ℕ) (q : Data)
    (bound : ∀ d, HaltsWithin p (.cons (encode n) d) (B * (d.size + 1) ^ k))
    (preserves : ∀ a, route (.cons (encode n) q) = (true, a) →
      ∃ d ctx, a = .cons (.cons (encode n) d) ctx) :
    HaltsWithin (routeOneCall route p post) (.cons (encode n) q)
      ((routeCost route post B k).eval (Data.cons (encode n) q).size) := by sorry
