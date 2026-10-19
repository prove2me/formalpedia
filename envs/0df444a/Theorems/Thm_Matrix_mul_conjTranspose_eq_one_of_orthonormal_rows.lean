-- Prove2me | Theorems.Thm_Matrix_mul_conjTranspose_eq_one_of_orthonormal_rows
-- name    : Matrix.mul_conjTranspose_eq_one_of_orthonormal_rows
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:17:43.459985+00:00
-- url     : https://prove2.me/theorems/50f0c921-443a-45a6-bb82-1e8c9db86ea1
-- title:
--   A matrix whose rows form an orthonormal family is a coisometry
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteHilbert` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Finite-dimensional Hilbert spaces. This file contains small reusable lemmas about finite-dimensional Hilbert spaces which are independent of the low individual degree test. The first ingredient is the elementary fact that a Hilbert space embeds linearly and isometrically into any finite-dimensional Hilbert space of at least the same dimension. The second translates this dimension-controlled isometry into a rectangular matrix with orthonormal rows.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   A matrix whose rows form an orthonormal family is a coisometry.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open Matrix
--   open Module
--
--   theorem Matrix.mul_conjTranspose_eq_one_of_orthonormal_rows
--       {𝕜 : Type*} [RCLike 𝕜]
--       {m n : Type*} [DecidableEq m] [Fintype n]
--       (row : m → EuclideanSpace 𝕜 n)
--       (hrow : Orthonormal 𝕜 row) :
--       (Matrix.of fun i j => row i j) * (Matrix.of fun i j => row i j)ᴴ =
--         (1 : Matrix m m 𝕜)
--   ```
--
--   **Formalization Note** `Matrix.mul_conjTranspose_eq_one_of_orthonormal_rows` is declared in `MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteHilbert.lean`, lines 77–95. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteHilbert.lean#L77-L95

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

open Matrix
open Module
set_option backward.isDefEq.respectTransparency false

theorem Matrix.mul_conjTranspose_eq_one_of_orthonormal_rows
    {𝕜 : Type*} [RCLike 𝕜]
    {m n : Type*} [DecidableEq m] [Fintype n]
    (row : m → EuclideanSpace 𝕜 n)
    (hrow : Orthonormal 𝕜 row) :
    (Matrix.of fun i j => row i j) * (Matrix.of fun i j => row i j)ᴴ =
      (1 : Matrix m m 𝕜) := by sorry
