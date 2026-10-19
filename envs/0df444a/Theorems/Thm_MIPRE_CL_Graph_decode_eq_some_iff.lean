-- Prove2me | Theorems.Thm_MIPRE_CL_Graph_decode_eq_some_iff
-- name    : MIPRE.CL.Graph.decode_eq_some_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:20:08.77025+00:00
-- url     : https://prove2.me/theorems/0d11339f-aefb-436f-85bb-3ac4b9b0764b
-- title:
--   Successful decoding means equality with the whole vertex-and-neighbor encoding
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.Graph` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The two-level graph sampler. The graph may have loops. Its law is uniform on ordered adjacent pairs, so each loop is counted once. This file supplies the semantic CL presentations; compiling their finite graph table into an ambient sampler program is a separate obligation.
--
--   Successful decoding means equality with the whole vertex-and-neighbor encoding.
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
--   theorem MIPRE.CL.Graph.decode_eq_some_iff (E : T → T → Prop) [DecidableRel E]
--       (x : Bool × T → ZMod 2) (u : T) : decode E x = some u ↔ x = encode E u
--   ```
--
--   **Formalization Note** `MIPRE.CL.Graph.decode_eq_some_iff` is declared in `MIPRE/Foundations/CL/Graph.lean`, lines 44–60. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Graph.lean#L44-L60

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

theorem MIPRE.CL.Graph.decode_eq_some_iff (E : T → T → Prop) [DecidableRel E]
    (x : Bool × T → ZMod 2) (u : T) : decode E x = some u ↔ x = encode E u := by sorry
