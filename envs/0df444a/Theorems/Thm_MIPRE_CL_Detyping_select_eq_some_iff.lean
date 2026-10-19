-- Prove2me | Theorems.Thm_MIPRE_CL_Detyping_select_eq_some_iff
-- name    : MIPRE.CL.Detyping.select_eq_some_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:19:50.655905+00:00
-- url     : https://prove2.me/theorems/7ee1c51b-af08-4d71-8645-a42661243147
-- title:
--   The exact specification of successful type selection
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.Detyping` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Detyped conditionally linear functions. The construction of `types.tex`, `def:detyped-CL`: run the graph sampler, then the selected typed presentation on an independent register. An invalid graph view selects a zero presentation that still consumes the whole content register. The conditional law retains the common content seed of both players. This file constructs the presentations and proves their law. The ambient program and its runtime are the separate `lem:detype-sampler` obligation.
--
--   The exact specification of successful type selection.
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
--   theorem MIPRE.CL.Detyping.select_eq_some_iff (E : T → T → Prop) [DecidableRel E] (w : Bool)
--       (g : Graph.Coord T → ZMod 2) (u : T) :
--       select E w g = some u ↔
--         (fun p => g (w, p)) = Graph.encode E u ∧ g (!w, (true, u)) = 1
--   ```
--
--   **Formalization Note** `MIPRE.CL.Detyping.select_eq_some_iff` is declared in `MIPRE/Foundations/CL/Detyping.lean`, lines 94–120. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Detyping.lean#L94-L120; blueprint lem:detype-cl

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

open MIPRE
open MIPRE.CL
open MIPRE.CL.Detyping
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]

theorem MIPRE.CL.Detyping.select_eq_some_iff (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (g : Graph.Coord T → ZMod 2) (u : T) :
    select E w g = some u ↔
      (fun p => g (w, p)) = Graph.encode E u ∧ g (!w, (true, u)) = 1 := by sorry
