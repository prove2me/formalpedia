-- Prove2me | Theorems.Thm_MIPRE_CL_Detyping_select_output
-- name    : MIPRE.CL.Detyping.select_output
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:19:49.619249+00:00
-- url     : https://prove2.me/theorems/b820cb56-ec0d-423d-a1b0-1905d8204faf
-- title:
--   Type selection is unchanged by passing from a seed to the sampled graph view
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.Detyping` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Detyped conditionally linear functions. The construction of `types.tex`, `def:detyped-CL`: run the graph sampler, then the selected typed presentation on an independent register. An invalid graph view selects a zero presentation that still consumes the whole content register. The conditional law retains the common content seed of both players. This file constructs the presentations and proves their law. The ambient program and its runtime are the separate `lem:detype-sampler` obligation.
--
--   Type selection is unchanged by passing from a seed to the sampled graph view.
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
--   theorem MIPRE.CL.Detyping.select_output (E : T → T → Prop) [DecidableRel E] (w : Bool)
--       (g : Graph.Coord T → ZMod 2) : select E w ((Graph.presentation E w).eval g) = select E w g
--   ```
--
--   **Formalization Note** `MIPRE.CL.Detyping.select_output` is declared in `MIPRE/Foundations/CL/Detyping.lean`, lines 122–140. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Detyping.lean#L122-L140; blueprint lem:detype-cl

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

theorem MIPRE.CL.Detyping.select_output (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (g : Graph.Coord T → ZMod 2) : select E w ((Graph.presentation E w).eval g) = select E w g := by sorry
