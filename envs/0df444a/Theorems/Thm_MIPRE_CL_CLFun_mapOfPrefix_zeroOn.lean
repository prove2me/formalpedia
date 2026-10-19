-- Prove2me | Theorems.Thm_MIPRE_CL_CLFun_mapOfPrefix_zeroOn
-- name    : MIPRE.CL.CLFun.mapOfPrefix_zeroOn
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:19:49.362988+00:00
-- url     : https://prove2.me/theorems/af7696bc-257d-46d8-810c-30b83e1515d6
-- title:
--   Fallback linear queries are zero for all prefixes and levels
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.Detyping` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Detyped conditionally linear functions. The construction of `types.tex`, `def:detyped-CL`: run the graph sampler, then the selected typed presentation on an independent register. An invalid graph view selects a zero presentation that still consumes the whole content register. The conditional law retains the common content seed of both players. This file constructs the presentations and proves their law. The ambient program and its runtime are the separate `lem:detype-sampler` obligation.
--
--   Fallback linear queries are zero for all prefixes and levels.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.CLFun
--   open Finset Classical
--   variable {F ι : Type*} [Semiring F] [DecidableEq ι]
--
--   theorem MIPRE.CL.CLFun.mapOfPrefix_zeroOn [Fintype ι] (S : Finset ι) (ℓ j : ℕ) (x : ι → F) :
--       (zeroOn (F := F) S ℓ).mapOfPrefix j x = 0
--   ```
--
--   **Formalization Note** `MIPRE.CL.CLFun.mapOfPrefix_zeroOn` is declared in `MIPRE/Foundations/CL/Detyping.lean`, lines 60–68. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Detyping.lean#L60-L68; blueprint lem:detype-queries

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
open MIPRE.CL.CLFun
open Finset Classical
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Semiring F] [DecidableEq ι]

theorem MIPRE.CL.CLFun.mapOfPrefix_zeroOn [Fintype ι] (S : Finset ι) (ℓ j : ℕ) (x : ι → F) :
    (zeroOn (F := F) S ℓ).mapOfPrefix j x = 0 := by sorry
