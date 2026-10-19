-- Prove2me | Theorems.Thm_MIPRE_sum_tensorFamily
-- name    : MIPRE.sum_tensorFamily
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:27:32.885971+00:00
-- url     : https://prove2.me/theorems/bdfcd1a8-b02d-4373-bbc7-1777eb4c7f79
-- title:
--   Lemma sum_tensorFamily of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.TensorFamily` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The Kronecker product of a family of matrices. The `k`-fold tensor product `M₁ ⊗ ⋯ ⊗ M_k` of matrices on `ℂ^ι`, as a matrix on `ℂ^{Fin k → ι}`: `(⊗ᵢ Mᵢ) v w = ∏ᵢ Mᵢ (v i) (w i)`. This is what the `k`-fold tensor power of a strategy measures with (`MIPRE.SyncStrategy.tensorPow`, `Background/Repetition/TensorPower.lean`), and the four facts about it that the value and PCC computations use: it is multiplicative (`tensorFamily_mul`), compatible with the adjoint (`tensorFamily_conjTranspose`), sends the constant family `1` to `1` (`tensorFamily_one`), sums coordinatewise (`sum_tensorFamily`) and…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Matrix
--   variable {k : ℕ} {ι : Type*}
--
--   theorem MIPRE.sum_tensorFamily {A : Type*} [Fintype A] (M : Fin k → A → Matrix ι ι ℂ) :
--       ∑ a : Fin k → A, tensorFamily (fun i => M i (a i)) = tensorFamily fun i => ∑ a, M i a
--   ```
--
--   **Formalization Note** `MIPRE.sum_tensorFamily` is declared in `MIPRE/Foundations/TensorFamily.lean`, lines 68–72. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/TensorFamily.lean#L68-L72

import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Definitions.Def_MIPRE_Foundations_TensorFamily

open MIPRE
open Matrix
variable {k : ℕ} {ι : Type*}

theorem MIPRE.sum_tensorFamily {A : Type*} [Fintype A] (M : Fin k → A → Matrix ι ι ℂ) :
    ∑ a : Fin k → A, tensorFamily (fun i => M i (a i)) = tensorFamily fun i => ∑ a, M i a := by sorry
