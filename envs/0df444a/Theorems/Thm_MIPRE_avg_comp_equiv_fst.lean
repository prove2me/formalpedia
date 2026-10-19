-- Prove2me | Theorems.Thm_MIPRE_avg_comp_equiv_fst
-- name    : MIPRE.avg_comp_equiv_fst
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:54:21.773534+00:00
-- url     : https://prove2.me/theorems/523e1800-51c1-47b8-b4dc-a8b47c71345d
-- title:
--   A uniform average of a function of one factor is the uniform average over that factor
-- statement:
--   A statement of the module `MIPRE.Foundations.Blocks` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Summing over assignments to a block-decomposed index type. A construction that reads only some coordinates of a uniformly random point needs to know that those coordinates are themselves uniform, and independent of the rest. In the form a sum identity takes, that is: when the index type is a sum, summing a function of the blocks' assignments over all assignments to the whole gives the iterated sum over the blocks --- once per assignment of whatever block the function ignores. * `sum_arrow_pair` --- both blocks, which is the product measure written as an iterated sum; * `sum_arrow_inl` --- the…
--
--   **A uniform average of a function of one factor is the uniform average over that factor.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset
--   variable {α β F M : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype F]
--   variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Nonempty α] [Nonempty γ]
--
--   theorem MIPRE.avg_comp_equiv_fst (e : α ≃ β × γ) (f : β → ℝ) :
--       ∑ a : α, (Fintype.card α : ℝ)⁻¹ * f (e a).1 = ∑ b : β, (Fintype.card β : ℝ)⁻¹ * f b
--   ```
--
--   **Formalization Note** `MIPRE.avg_comp_equiv_fst` is declared in `MIPRE/Foundations/Blocks.lean`, lines 170–185. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Blocks.lean#L170-L185; blueprint lem:qld-padded-lines

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Blocks

open MIPRE
open Finset
variable {α β F M : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype F]
  [AddCommMonoid M]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Nonempty α] [Nonempty γ]

theorem MIPRE.avg_comp_equiv_fst (e : α ≃ β × γ) (f : β → ℝ) :
    ∑ a : α, (Fintype.card α : ℝ)⁻¹ * f (e a).1 = ∑ b : β, (Fintype.card β : ℝ)⁻¹ * f b := by sorry
