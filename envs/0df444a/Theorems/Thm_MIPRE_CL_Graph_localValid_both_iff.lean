-- Prove2me | Theorems.Thm_MIPRE_CL_Graph_localValid_both_iff
-- name    : MIPRE.CL.Graph.localValid_both_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:20:09.50175+00:00
-- url     : https://prove2.me/theorems/dc828c57-41b8-42ca-92c6-a242a574a59a
-- title:
--   Both local valid views are exactly the encodings of adjacent ordered pairs
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.Graph` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The two-level graph sampler. The graph may have loops. Its law is uniform on ordered adjacent pairs, so each loop is counted once. This file supplies the semantic CL presentations; compiling their finite graph table into an ambient sampler program is a separate obligation.
--
--   Both local valid views are exactly the encodings of adjacent ordered pairs.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.Graph
--   open Finset Classical
--   variable {T : Type*} [Fintype T] [DecidableEq T]
--
--   theorem MIPRE.CL.Graph.localValid_both_iff (E : T → T → Prop) [DecidableRel E]
--       (hE : ∀ u v, E u v → E v u) (z : Coord T → ZMod 2) :
--       localValid E false z ∧ localValid E true z ↔
--         ∃ uv : T × T, E uv.1 uv.2 ∧ z = pairSeed E uv
--   ```
--
--   **Formalization Note** `MIPRE.CL.Graph.localValid_both_iff` is declared in `MIPRE/Foundations/CL/Graph.lean`, lines 199–222. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Graph.lean#L199-L222; blueprint lem:detype-graph

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Graph

open MIPRE
open MIPRE.CL
open MIPRE.CL.Graph
open Finset Classical
variable {T : Type*} [Fintype T] [DecidableEq T]

theorem MIPRE.CL.Graph.localValid_both_iff (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (z : Coord T → ZMod 2) :
    localValid E false z ∧ localValid E true z ↔
      ∃ uv : T × T, E uv.1 uv.2 ∧ z = pairSeed E uv := by sorry
