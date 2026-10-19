-- Prove2me | Theorems.Thm_MIPRE_tensorFamily_one
-- name    : MIPRE.tensorFamily_one
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:27:26.796246+00:00
-- url     : https://prove2.me/theorems/918d6a50-e056-4ce0-a7c8-f2817192a106
-- title:
--   Lemma tensorFamily_one of the MIP* = RE formalization
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
--   theorem MIPRE.tensorFamily_one [DecidableEq ι] : tensorFamily (fun _ : Fin k => (1 : Matrix ι ι ℂ)) = 1
--   ```
--
--   **Formalization Note** `MIPRE.tensorFamily_one` is declared in `MIPRE/Foundations/TensorFamily.lean`, lines 55–61. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/TensorFamily.lean#L55-L61

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

theorem MIPRE.tensorFamily_one [DecidableEq ι] : tensorFamily (fun _ : Fin k => (1 : Matrix ι ι ℂ)) = 1 := by sorry
