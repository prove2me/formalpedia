-- Prove2me | Theorems.Thm_MIPRE_IsPVM_coarse
-- name    : MIPRE.IsPVM.coarse
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:25:51.473986+00:00
-- url     : https://prove2.me/theorems/1b2cf0b7-2e3a-451a-acbd-379d56e923de
-- title:
--   Coarse-graining a projective measurement gives a projective measurement. Summing the elements over a level set of f preserves self-adjointness, and mutual orthogonality…
-- statement:
--   A statement of the module `MIPRE.Foundations.PVM` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Observables of a projective measurement. A projective measurement `P : Λ → Matrix n n ℂ` and a weighting `ε : Λ → ℂ` give the operator `pvmObs P ε = ∑_a ε a • P a`. The one fact worth isolating is that this is a **ring homomorphism** in `ε`: `pvmObs P ε * pvmObs P δ = pvmObs P (ε * δ)`, `pvmObs P 1 = 1`, because the projections are mutually orthogonal (`IsPVM.orthogonal`). Everything the rigidity arguments want about signed sums of a projective measurement follows: with `ε` valued in `{±1}`, `pvmObs P ε` is a self-adjoint reflection; two weightings of the *same* measurement commute, whatever…
--
--   **Coarse-graining a projective measurement gives a projective measurement.** Summing the
--   elements over a level set of `f` preserves self-adjointness, and mutual orthogonality
--   (`IsPVM.orthogonal`) makes the sum idempotent; the level sets partition the outcomes, so the sums
--   still add to one. This is what makes the expansion stage's convolutions projective.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder
--   variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
--   variable {P : Λ → Matrix n n ℂ}
--
--   theorem MIPRE.IsPVM.coarse {Λ' : Type*} [Fintype Λ'] [DecidableEq Λ'] (h : IsPVM P) (f : Λ → Λ') :
--       IsPVM (fun c => ∑ a ∈ univ.filter fun a => f a = c, P a)
--   ```
--
--   **Formalization Note** `MIPRE.IsPVM.coarse` is declared in `MIPRE/Foundations/PVM.lean`, lines 100–117. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/PVM.lean#L100-L117; blueprint def:expanded-state

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_PVM

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → Matrix n n ℂ}

theorem MIPRE.IsPVM.coarse {Λ' : Type*} [Fintype Λ'] [DecidableEq Λ'] (h : IsPVM P) (f : Λ → Λ') :
    IsPVM (fun c => ∑ a ∈ univ.filter fun a => f a = c, P a) := by sorry
