-- Prove2me | Theorems.Thm_MIPRE_CL_Detyping_marginal_content
-- name    : MIPRE.CL.Detyping.marginal_content
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:30.988683+00:00
-- url     : https://prove2.me/theorems/86e9ef11-83a4-4a7a-a58e-a8d520bfd9f9
-- title:
--   Later marginals pair the full graph question with the selected content marginal
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingQueries` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Query routing for the detyped CL presentation. The semantic specification of all branches of `types.tex`, `def:detyped-sampler`. The level indices of factor and linear queries are zero based, as in `CLFun`. These are equalities of the actual presentations' queries, not extra assumptions on a future sampler program.
--
--   Later marginals pair the full graph question with the selected content marginal.
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
--   theorem MIPRE.CL.Detyping.marginal_content {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
--       (P : T → CLFun (ZMod 2) ι ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ)
--       (j : ℕ) (x : Coord T ι → ZMod 2) :
--       ((presentation E w P).truncate (j + 2)).eval x = Sum.elim
--         ((Graph.presentation E w).eval (pull .inl x))
--         (((selected P (select E w (pull .inl x))).truncate j).eval (pull .inr x))
--   ```
--
--   **Formalization Note** `MIPRE.CL.Detyping.marginal_content` is declared in `MIPRE/Foundations/CL/DetypingQueries.lean`, lines 90–107. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingQueries.lean#L90-L107; blueprint lem:detype-queries

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
open MIPRE.CL.Detyping
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]

theorem MIPRE.CL.Detyping.marginal_content {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (j : ℕ) (x : Coord T ι → ZMod 2) :
    ((presentation E w P).truncate (j + 2)).eval x = Sum.elim
      ((Graph.presentation E w).eval (pull .inl x))
      (((selected P (select E w (pull .inl x))).truncate j).eval (pull .inr x)) := by sorry
