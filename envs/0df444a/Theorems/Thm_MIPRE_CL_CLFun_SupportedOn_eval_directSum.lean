-- Prove2me | Theorems.Thm_MIPRE_CL_CLFun_SupportedOn_eval_directSum
-- name    : MIPRE.CL.CLFun.SupportedOn.eval_directSum
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:54:25.587688+00:00
-- url     : https://prove2.me/theorems/ebacd3b8-67b6-434c-9e81-e7fae10fbb4b
-- title:
--   The direct sum presents the sum of the two functions, when they are on disjoint register subspaces
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.Closure` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Closure properties of conditionally linear functions, and CL distributions. Paper `linear.tex`: concatenation (`lem:cl-concat`) and direct sums (`lem:cl-func-prod`) of conditionally linear functions, and the conditionally linear distribution of a pair of CL functions (`def:cl-dist`); blueprint `def:cl-function` and `lem:cl-closure`, ledger node `1.1.2`. Both constructions are on presentations (`MIPRE.CL.CLFun`) and are hypothesis-free; the hypotheses of the paper's lemmas — the pieces live on disjoint register subspaces — enter only in the evaluation lemmas (`SupportedOn.eval_concat`,…
--
--   The direct sum presents the sum of the two functions, when they are on disjoint register
--   subspaces.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.CLFun
--   variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {k ℓ : ℕ}
--   variable [Fintype ι]
--
--   theorem MIPRE.CL.CLFun.SupportedOn.eval_directSum {P Q : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
--       (hQ : Q.SupportedOn T') (hTT' : Disjoint T T') (x : ι → F) :
--       (P.directSum Q).eval x = P.eval x + Q.eval x
--   ```
--
--   **Formalization Note** `MIPRE.CL.CLFun.SupportedOn.eval_directSum` is declared in `MIPRE/Foundations/CL/Closure.lean`, lines 176–218. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Closure.lean#L176-L218

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure_B

open MIPRE
open MIPRE.CL
open MIPRE.CL.CLFun
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {k ℓ : ℕ}
variable [Fintype ι]

theorem MIPRE.CL.CLFun.SupportedOn.eval_directSum {P Q : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
    (hQ : Q.SupportedOn T') (hTT' : Disjoint T T') (x : ι → F) :
    (P.directSum Q).eval x = P.eval x + Q.eval x := by sorry
