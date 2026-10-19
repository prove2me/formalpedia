-- Prove2me | Theorems.Thm_MIPRE_CL_CLFun_SupportedOn_mapAt_apply_proj
-- name    : MIPRE.CL.CLFun.SupportedOn.mapAt_apply_proj
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:54:21.197651+00:00
-- url     : https://prove2.me/theorems/73237002-c69a-4d9d-9ecd-a0dcf46efa85
-- title:
--   The stage maps of a presentation on V_T read only the coordinates in T
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.Basic` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Conditionally linear functions. Blueprint `def:cl-function` (paper `linear.tex`, Definition `def:cl-func`; ledger node `1.1.2`). The question distribution of every game in the pipeline is *conditionally linear*: linear maps applied in stages to complementary register subspaces of `V = F^ι`, the register subspace and the linear map of each stage being allowed to depend on the outputs of the previous stages.
--
--   The stage maps of a presentation on `V_T` read only the coordinates in `T`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.CLFun
--   variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
--   variable [Fintype ι]
--
--   theorem MIPRE.CL.CLFun.SupportedOn.mapAt_apply_proj {P : CLFun F ι ℓ} {T U : Finset ι} (hP : P.SupportedOn T)
--       (hTU : T ⊆ U) (k : ℕ) (x y : ι → F) : P.mapAt k x (proj U y) = P.mapAt k x y
--   ```
--
--   **Formalization Note** `MIPRE.CL.CLFun.SupportedOn.mapAt_apply_proj` is declared in `MIPRE/Foundations/CL/Basic.lean`, lines 351–364. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Basic.lean#L351-L364

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic

open MIPRE
open MIPRE.CL
open MIPRE.CL.CLFun
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]

theorem MIPRE.CL.CLFun.SupportedOn.mapAt_apply_proj {P : CLFun F ι ℓ} {T U : Finset ι} (hP : P.SupportedOn T)
    (hTU : T ⊆ U) (k : ℕ) (x y : ι → F) : P.mapAt k x (proj U y) = P.mapAt k x y := by sorry
