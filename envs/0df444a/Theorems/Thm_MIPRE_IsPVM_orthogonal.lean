-- Prove2me | Theorems.Thm_MIPRE_IsPVM_orthogonal
-- name    : MIPRE.IsPVM.orthogonal
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:25:52.515979+00:00
-- url     : https://prove2.me/theorems/90263e85-9d5e-4f7b-9955-2e3bb842684e
-- title:
--   The elements of a projective measurement are mutually orthogonal. Conjugating ∑_c P c = 1 by P a makes the off-diagonal compressions a family of positive matrices summing…
-- statement:
--   A statement of the module `MIPRE.Foundations.PVM` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Observables of a projective measurement. A projective measurement `P : Λ → Matrix n n ℂ` and a weighting `ε : Λ → ℂ` give the operator `pvmObs P ε = ∑_a ε a • P a`. The one fact worth isolating is that this is a **ring homomorphism** in `ε`: `pvmObs P ε * pvmObs P δ = pvmObs P (ε * δ)`, `pvmObs P 1 = 1`, because the projections are mutually orthogonal (`IsPVM.orthogonal`). Everything the rigidity arguments want about signed sums of a projective measurement follows: with `ε` valued in `{±1}`, `pvmObs P ε` is a self-adjoint reflection; two weightings of the *same* measurement commute, whatever…
--
--   **The elements of a projective measurement are mutually orthogonal.** Conjugating
--   `∑_c P c = 1` by `P a` makes the off-diagonal compressions a family of positive matrices
--   summing to zero, so each is zero, and `P a P b P a = 0` forces `P b P a = 0`.
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
--   theorem MIPRE.IsPVM.orthogonal (h : IsPVM P) {a b : Λ} (hab : a ≠ b) : P a * P b = 0
--   ```
--
--   **Formalization Note** `MIPRE.IsPVM.orthogonal` is declared in `MIPRE/Foundations/PVM.lean`, lines 63–98. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/PVM.lean#L63-L98

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_PVM

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → Matrix n n ℂ}

theorem MIPRE.IsPVM.orthogonal (h : IsPVM P) {a b : Λ} (hab : a ≠ b) : P a * P b = 0 := by sorry
