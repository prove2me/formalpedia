-- Prove2me | Theorems.Thm_MIPRE_CL_proj_add_proj_compl
-- name    : MIPRE.CL.proj_add_proj_compl
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:20:55.821975+00:00
-- url     : https://prove2.me/theorems/f98e028b-6ba2-4b39-851f-ec9b06a67dce
-- title:
--   Lemma proj_add_proj_compl of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.Register` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Register subspaces. The linear spaces of the conditionally linear machinery (blueprint `sec:ps-cl`, paper `linear.tex`) are `V = F^ι` for a finite index type `ι`, and the subspaces that occur in it are *register subspaces*: spans of subsets of the standard basis, hence determined by a set `S : Finset ι` of coordinates (paper `preliminaries.tex`, "Register subspace"). This file fixes the two pieces of vocabulary in which everything else is written. * `MIPRE.CL.proj S : (ι → F) →ₗ[F] (ι → F)` is the coordinate projection onto `V_S` along the complementary register subspace `V_{Sᶜ}`: the paper's…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
--
--   theorem MIPRE.CL.proj_add_proj_compl [Fintype ι] (S : Finset ι) (x : ι → F) :
--       proj S x + proj Sᶜ x = x
--   ```
--
--   **Formalization Note** `MIPRE.CL.proj_add_proj_compl` is declared in `MIPRE/Foundations/CL/Register.lean`, lines 73–75. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Register.lean#L73-L75

import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register

open MIPRE
open MIPRE.CL
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]

theorem MIPRE.CL.proj_add_proj_compl [Fintype ι] (S : Finset ι) (x : ι → F) :
    proj S x + proj Sᶜ x = x := by sorry
