-- Prove2me | Theorems.Thm_MIPRE_CL_Detyping_graph_output_of_select
-- name    : MIPRE.CL.Detyping.graph_output_of_select
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:19:56.004318+00:00
-- url     : https://prove2.me/theorems/7b36af75-9c56-4cb5-ae87-eb16ed1205a8
-- title:
--   Every valid local sample is exactly the fixed graph question of its selected type
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingLaw` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The joint law of detyped questions. On an ordered edge the graph view depends only on the player's own type. Conditioning on the valid-edge event gives the uniform ordered-edge law and one shared uniform content seed, exactly as in `types.tex`, `def:detyped-CL`.
--
--   Every valid local sample is exactly the fixed graph question of its selected type.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.Detyping
--   open Finset Classical
--   variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
--
--   theorem MIPRE.CL.Detyping.graph_output_of_select (E : T → T → Prop) [DecidableRel E] (w : Bool)
--       (g : Graph.Coord T → ZMod 2) {u : T} (h : select E w g = some u) :
--       (Graph.presentation E w).eval g = view E w u
--   ```
--
--   **Formalization Note** `MIPRE.CL.Detyping.graph_output_of_select` is declared in `MIPRE/Foundations/CL/DetypingLaw.lean`, lines 28–46. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingLaw.lean#L28-L46; blueprint lem:detype-cl

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw

open MIPRE
open MIPRE.CL
open MIPRE.CL.Detyping
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]

theorem MIPRE.CL.Detyping.graph_output_of_select (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (g : Graph.Coord T → ZMod 2) {u : T} (h : select E w g = some u) :
    (Graph.presentation E w).eval g = view E w u := by sorry
