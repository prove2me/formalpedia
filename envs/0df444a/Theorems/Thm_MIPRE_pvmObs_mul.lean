-- Prove2me | Theorems.Thm_MIPRE_pvmObs_mul
-- name    : MIPRE.pvmObs_mul
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:12:56.979395+00:00
-- url     : https://prove2.me/theorems/97ea4693-054e-4380-9184-48c4d69ee0ca
-- title:
--   pvmObs P is multiplicative. This is the whole content of the file
-- statement:
--   A statement of the module `MIPRE.Foundations.PVM` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Observables of a projective measurement. A projective measurement `P : Λ → Matrix n n ℂ` and a weighting `ε : Λ → ℂ` give the operator `pvmObs P ε = ∑_a ε a • P a`. The one fact worth isolating is that this is a **ring homomorphism** in `ε`: `pvmObs P ε * pvmObs P δ = pvmObs P (ε * δ)`, `pvmObs P 1 = 1`, because the projections are mutually orthogonal (`IsPVM.orthogonal`). Everything the rigidity arguments want about signed sums of a projective measurement follows: with `ε` valued in `{±1}`, `pvmObs P ε` is a self-adjoint reflection; two weightings of the *same* measurement commute, whatever…
--
--   **`pvmObs P` is multiplicative.** This is the whole content of the file.
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
--   theorem MIPRE.pvmObs_mul (h : IsPVM P) (ε δ : Λ → ℂ) :
--       pvmObs P ε * pvmObs P δ = pvmObs P (ε * δ)
--   ```
--
--   **Formalization Note** `MIPRE.pvmObs_mul` is declared in `MIPRE/Foundations/PVM.lean`, lines 136–149. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/PVM.lean#L136-L149

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → Matrix n n ℂ}

theorem MIPRE.pvmObs_mul (h : IsPVM P) (ε δ : Λ → ℂ) :
    pvmObs P ε * pvmObs P δ = pvmObs P (ε * δ) := by sorry
