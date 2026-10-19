-- Prove2me | Theorems.Thm_MIPRE_CL_CLFun_zeroOn_exactlyOn
-- name    : MIPRE.CL.CLFun.zeroOn_exactlyOn
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:54:39.230543+00:00
-- url     : https://prove2.me/theorems/84ea31a9-34e0-422c-852f-7e0e0b926cff
-- title:
--   The zero fallback still partitions all registers when at least one level is available
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.Detyping` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Detyped conditionally linear functions. The construction of `types.tex`, `def:detyped-CL`: run the graph sampler, then the selected typed presentation on an independent register. An invalid graph view selects a zero presentation that still consumes the whole content register. The conditional law retains the common content seed of both players. This file constructs the presentations and proves their law. The ambient program and its runtime are the separate `lem:detype-sampler` obligation.
--
--   The zero fallback still partitions all registers when at least one level is available.
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
--   theorem MIPRE.CL.CLFun.zeroOn_exactlyOn (S : Finset ι) (ℓ : ℕ) (h : ℓ = 0 → S = ∅) :
--       (zeroOn (F := F) S ℓ).ExactlyOn S
--   ```
--
--   **Formalization Note** `MIPRE.CL.CLFun.zeroOn_exactlyOn` is declared in `MIPRE/Foundations/CL/Detyping.lean`, lines 37–44. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Detyping.lean#L37-L44; blueprint lem:detype-queries

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

theorem MIPRE.CL.CLFun.zeroOn_exactlyOn (S : Finset ι) (ℓ : ℕ) (h : ℓ = 0 → S = ∅) :
    (zeroOn (F := F) S ℓ).ExactlyOn S := by sorry
