-- Prove2me | Theorems.Thm_MIPRE_CL_CLFun_mapOfPrefix_reindex
-- name    : MIPRE.CL.CLFun.mapOfPrefix_reindex
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:20:12.632846+00:00
-- url     : https://prove2.me/theorems/eac43482-4218-48c3-a880-b31385278524
-- title:
--   Lemma mapOfPrefix_reindex of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.Downsize` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Downsizing conditionally linear functions, and reindexing. Paper `linear.tex`, `def:cl-downsize`, `lem:cl-downsize` and `lem:downsize-cl-dist`; blueprint `lem:cl-downsize`. The CL functions of the pipeline are native to `𝔽_{2^t}` (the low-degree tests, the introspection sampler), while samplers of normal form verifiers are over `𝔽₂` (`def:sampler`). *Downsizing* bridges the two: a basis `b` of a field `F` over a subfield `K` gives the `K`-linear bijection `↓ : F^ι ≃ K^{ι × κ}` reading off coordinates entry by entry (`downsizeEquiv`), and `L ↦ ↓ ∘ L ∘ ↓⁻¹` carries `ℓ`-level CL functions on…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.CLFun
--   variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
--   variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
--   variable [DecidableEq ι] [DecidableEq κ]
--   variable [Fintype ι]
--   variable [DecidableEq ι'] [Fintype ι']
--   variable {ℓ : ℕ}
--
--   theorem MIPRE.CL.CLFun.mapOfPrefix_reindex (e : ι ≃ ι') (P : CLFun F ι ℓ) (k : ℕ) (u : ι → F) :
--       (P.reindex e).mapOfPrefix k (reindexEquiv e u) =
--         (reindexEquiv e).toLinearMap ∘ₗ P.mapOfPrefix k u ∘ₗ (reindexEquiv e).symm.toLinearMap
--   ```
--
--   **Formalization Note** `MIPRE.CL.CLFun.mapOfPrefix_reindex` is declared in `MIPRE/Foundations/CL/Downsize.lean`, lines 404–414. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Downsize.lean#L404-L414

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Downsize

open MIPRE
open MIPRE.CL
open MIPRE.CL.CLFun
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable [DecidableEq ι'] [Fintype ι']
variable {ℓ : ℕ}

theorem MIPRE.CL.CLFun.mapOfPrefix_reindex (e : ι ≃ ι') (P : CLFun F ι ℓ) (k : ℕ) (u : ι → F) :
    (P.reindex e).mapOfPrefix k (reindexEquiv e u) =
      (reindexEquiv e).toLinearMap ∘ₗ P.mapOfPrefix k u ∘ₗ (reindexEquiv e).symm.toLinearMap := by sorry
