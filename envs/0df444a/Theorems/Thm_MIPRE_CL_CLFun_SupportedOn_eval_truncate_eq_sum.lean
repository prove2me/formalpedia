-- Prove2me | Theorems.Thm_MIPRE_CL_CLFun_SupportedOn_eval_truncate_eq_sum
-- name    : MIPRE.CL.CLFun.SupportedOn.eval_truncate_eq_sum
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:54:22.483553+00:00
-- url     : https://prove2.me/theorems/59850f5c-32c9-4c72-bee2-dd2453912200
-- title:
--   Item (3) of lem:cl-kth: L_{≤k}(x) = ∑_{i ≤ k} x^{L_i}, the marginal is the sum of the stage maps applied to the input
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.Basic` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Conditionally linear functions. Blueprint `def:cl-function` (paper `linear.tex`, Definition `def:cl-func`; ledger node `1.1.2`). The question distribution of every game in the pipeline is *conditionally linear*: linear maps applied in stages to complementary register subspaces of `V = F^ι`, the register subspace and the linear map of each stage being allowed to depend on the outputs of the previous stages.
--
--   Item (3) of `lem:cl-kth`: `L_{≤k}(x) = ∑_{i ≤ k} x^{L_i}`, the marginal is the sum of the
--   stage maps applied to the input.
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
--   theorem MIPRE.CL.CLFun.SupportedOn.eval_truncate_eq_sum {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T)
--       (k : ℕ) (x : ι → F) : (P.truncate k).eval x = ∑ i ∈ Finset.range k, P.mapAt i x x
--   ```
--
--   **Formalization Note** `MIPRE.CL.CLFun.SupportedOn.eval_truncate_eq_sum` is declared in `MIPRE/Foundations/CL/Basic.lean`, lines 366–384. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Basic.lean#L366-L384; blueprint lem:cl-structure

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

theorem MIPRE.CL.CLFun.SupportedOn.eval_truncate_eq_sum {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T)
    (k : ℕ) (x : ι → F) : (P.truncate k).eval x = ∑ i ∈ Finset.range k, P.mapAt i x x := by sorry
