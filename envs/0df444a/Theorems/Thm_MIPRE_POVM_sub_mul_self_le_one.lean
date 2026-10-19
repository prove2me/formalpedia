-- Prove2me | Theorems.Thm_MIPRE_POVM_sub_mul_self_le_one
-- name    : MIPRE.POVM.sub_mul_self_le_one
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:12:36.444437+00:00
-- url     : https://prove2.me/theorems/5afd73fb-17e3-4076-ba9f-4faa4488a86a
-- title:
--   The difference of two POVM elements is a self-adjoint contraction. This is what makes a two-outcome coarse-graining of a POVM a ±1-observable in every estimate: X† = X and…
-- statement:
--   A statement of the module `MIPRE.Foundations.POVMValue` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The value of a POVM strategy, and its conditional failures. `MIPRE.TensorProductStrategy` is projective by construction, which is the right definition of the quantum value (`lem:povm-value-eq` says allowing POVMs changes nothing). But a *soundness* argument often has to start from an arbitrary POVM strategy --- blueprint `lem:ms-direct-anticomm` is stated for one, and its whole point is that no projectivity is assumed --- so this file gives the unbundled value of a POVM strategy and the conditional failure probabilities that soundness arguments actually consume. Nothing here is bundled into a…
--
--   **The difference of two POVM elements is a self-adjoint contraction.** This is what makes a
--   two-outcome coarse-graining of a POVM a `±1`-observable in every estimate: `X† = X` and
--   `X† X ≤ 1`, with no projectivity. Outcomes other than the two chosen contribute nothing.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix Kronecker
--   open scoped ComplexOrder MatrixOrder
--
--   theorem MIPRE.POVM.sub_mul_self_le_one {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d]
--       (M : POVM A d) (p q : A) :
--       (((M.mats p).val - (M.mats q).val) * ((M.mats p).val - (M.mats q).val))
--         ≤ (1 : Matrix d d ℂ)
--   ```
--
--   **Formalization Note** `MIPRE.POVM.sub_mul_self_le_one` is declared in `MIPRE/Foundations/POVMValue.lean`, lines 91–115. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/POVMValue.lean#L91-L115

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_POVMValue

open MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder

theorem MIPRE.POVM.sub_mul_self_le_one {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d]
    (M : POVM A d) (p q : A) :
    (((M.mats p).val - (M.mats q).val) * ((M.mats p).val - (M.mats q).val))
      ≤ (1 : Matrix d d ℂ) := by sorry
