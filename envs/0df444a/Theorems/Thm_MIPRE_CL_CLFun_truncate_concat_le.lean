-- Prove2me | Theorems.Thm_MIPRE_CL_CLFun_truncate_concat_le
-- name    : MIPRE.CL.CLFun.truncate_concat_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:26.995995+00:00
-- url     : https://prove2.me/theorems/1d391732-6090-4dfa-abe4-052ccbdfe32f
-- title:
--   Truncation inside the first part never visits a concatenation's continuation
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingQueries` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Query routing for the detyped CL presentation. The semantic specification of all branches of `types.tex`, `def:detyped-sampler`. The level indices of factor and linear queries are zero based, as in `CLFun`. These are equalities of the actual presentations' queries, not extra assumptions on a future sampler program.
--
--   Truncation inside the first part never visits a concatenation's continuation.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.CLFun
--   open Finset Classical
--   variable {F ι : Type*} [Semiring F] [DecidableEq ι] {k ℓ : ℕ}
--
--   theorem MIPRE.CL.CLFun.truncate_concat_le (L : CLFun F ι k) (R : (ι → F) → CLFun F ι ℓ)
--       (j : ℕ) (hj : j ≤ k) : (L.concat R).truncate j = L.truncate j
--   ```
--
--   **Formalization Note** `MIPRE.CL.CLFun.truncate_concat_le` is declared in `MIPRE/Foundations/CL/DetypingQueries.lean`, lines 36–51. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingQueries.lean#L36-L51

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
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries

open MIPRE
open MIPRE.CL
open MIPRE.CL.CLFun
open Finset Classical
variable {F ι : Type*} [Semiring F] [DecidableEq ι] {k ℓ : ℕ}

theorem MIPRE.CL.CLFun.truncate_concat_le (L : CLFun F ι k) (R : (ι → F) → CLFun F ι ℓ)
    (j : ℕ) (hj : j ≤ k) : (L.concat R).truncate j = L.truncate j := by sorry
