-- Prove2me | Theorems.Thm_MIPRE_CL_CLFun_ExactlyOn_concat
-- name    : MIPRE.CL.CLFun.ExactlyOn.concat
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:19:37.977108+00:00
-- url     : https://prove2.me/theorems/843a4905-7479-46d6-a0b4-29a7e5fe2037
-- title:
--   Lemma concat of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.Closure` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Closure properties of conditionally linear functions, and CL distributions. Paper `linear.tex`: concatenation (`lem:cl-concat`) and direct sums (`lem:cl-func-prod`) of conditionally linear functions, and the conditionally linear distribution of a pair of CL functions (`def:cl-dist`); blueprint `def:cl-function` and `lem:cl-closure`, ledger node `1.1.2`. Both constructions are on presentations (`MIPRE.CL.CLFun`) and are hypothesis-free; the hypotheses of the paper's lemmas — the pieces live on disjoint register subspaces — enter only in the evaluation lemmas (`SupportedOn.eval_concat`,…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.CLFun
--   variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {k ℓ : ℕ}
--
--   theorem MIPRE.CL.CLFun.ExactlyOn.concat {L : CLFun F ι k} {R : (ι → F) → CLFun F ι ℓ} {U W : Finset ι}
--       (hL : L.ExactlyOn U) (hR : ∀ u, (R u).ExactlyOn W) (hUW : Disjoint U W) :
--       (L.concat R).ExactlyOn (U ∪ W)
--   ```
--
--   **Formalization Note** `MIPRE.CL.CLFun.ExactlyOn.concat` is declared in `MIPRE/Foundations/CL/Closure.lean`, lines 77–90. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Closure.lean#L77-L90

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B

open MIPRE
open MIPRE.CL
open MIPRE.CL.CLFun
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {k ℓ : ℕ}

theorem MIPRE.CL.CLFun.ExactlyOn.concat {L : CLFun F ι k} {R : (ι → F) → CLFun F ι ℓ} {U W : Finset ι}
    (hL : L.ExactlyOn U) (hR : ∀ u, (R u).ExactlyOn W) (hUW : Disjoint U W) :
    (L.concat R).ExactlyOn (U ∪ W) := by sorry
