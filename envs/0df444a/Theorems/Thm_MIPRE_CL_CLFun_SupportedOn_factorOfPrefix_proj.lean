-- Prove2me | Theorems.Thm_MIPRE_CL_CLFun_SupportedOn_factorOfPrefix_proj
-- name    : MIPRE.CL.CLFun.SupportedOn.factorOfPrefix_proj
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:20:10.358324+00:00
-- url     : https://prove2.me/theorems/988b64e0-aa0f-4406-a7f5-6e6a99202c67
-- title:
--   A presentation on V_T reads its prefix only on T
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.Product` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Padding to a given level, and the product of two presentations. Two constructions the answer-reduced sampler needs (`sec:ar-verifier`, `ld_compiler.tex`): its CL functions are the direct sums of the oracularized sampler's, with `ℓ` levels, and the downsized PCP sampler's, with three, on disjoint registers, at the common level `max ℓ 3`. * `CLFun.liftTo T L h P` pads `P` with trivial levels to exactly `L ≥ ℓ` levels (`liftN` pads by a number of levels, and `ℓ + (L - ℓ)` is not `L` by definition, so the level is cast along `castLevel`). Evaluation and exactness are unchanged (`eval_liftTo`,…
--
--   A presentation on `V_T` reads its prefix only on `T`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.CLFun
--   open Finset
--   variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
--   variable {ℓ : ℕ}
--   variable [Fintype ι]
--
--   theorem MIPRE.CL.CLFun.SupportedOn.factorOfPrefix_proj {P : CLFun F ι ℓ} {T U : Finset ι} (hP : P.SupportedOn T)
--       (h : T ⊆ U) (j : ℕ) (u : ι → F) : P.factorOfPrefix j (proj U u) = P.factorOfPrefix j u
--   ```
--
--   **Formalization Note** `MIPRE.CL.CLFun.SupportedOn.factorOfPrefix_proj` is declared in `MIPRE/Foundations/CL/Product.lean`, lines 117–132. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Product.lean#L117-L132

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Product

open MIPRE
open MIPRE.CL
open MIPRE.CL.CLFun
open Finset
variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
variable [Fintype ι]

theorem MIPRE.CL.CLFun.SupportedOn.factorOfPrefix_proj {P : CLFun F ι ℓ} {T U : Finset ι} (hP : P.SupportedOn T)
    (h : T ⊆ U) (j : ℕ) (u : ι → F) : P.factorOfPrefix j (proj U u) = P.factorOfPrefix j u := by sorry
