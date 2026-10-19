-- Prove2me | Theorems.Thm_MIPRE_CL_pull_proj_compl
-- name    : MIPRE.CL.pull_proj_compl
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:20:06.839219+00:00
-- url     : https://prove2.me/theorems/91b1c174-7af0-41b1-a5a1-62e3ef477148
-- title:
--   Restriction of the projection onto the remaining registers
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.Embedding` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Embedding conditionally linear presentations in a larger register. Extending a presentation by zero along an injection preserves its evaluation, marginal, factor and linear-map queries. This puts the graph and content parts of detyping on disjoint registers without changing their query interfaces.
--
--   Restriction of the projection onto the remaining registers.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open Classical
--   variable {F ι κ : Type*} [Semiring F] [DecidableEq ι] [DecidableEq κ]
--
--   theorem MIPRE.CL.pull_proj_compl [Fintype ι] [Fintype κ] (e : ι ↪ κ) (S : Finset ι)
--       (x : κ → F) : pull e (proj (S.map e)ᶜ x) = proj Sᶜ (pull e x)
--   ```
--
--   **Formalization Note** `MIPRE.CL.pull_proj_compl` is declared in `MIPRE/Foundations/CL/Embedding.lean`, lines 75–79. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Embedding.lean#L75-L79

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Embedding

open MIPRE
open MIPRE.CL
open Classical
set_option linter.unusedSectionVars false
variable {F ι κ : Type*} [Semiring F] [DecidableEq ι] [DecidableEq κ]

theorem MIPRE.CL.pull_proj_compl [Fintype ι] [Fintype κ] (e : ι ↪ κ) (S : Finset ι)
    (x : κ → F) : pull e (proj (S.map e)ᶜ x) = proj Sᶜ (pull e x) := by sorry
