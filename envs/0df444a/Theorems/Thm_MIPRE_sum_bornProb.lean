-- Prove2me | Theorems.Thm_MIPRE_sum_bornProb
-- name    : MIPRE.sum_bornProb
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:25:14.264979+00:00
-- url     : https://prove2.me/theorems/321a50a6-864c-41c1-8143-414e1aae26e7
-- title:
--   The Born probabilities of a pair of POVMs sum to one
-- statement:
--   A statement of the module `MIPRE.Foundations.POVMValue` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The value of a POVM strategy, and its conditional failures. `MIPRE.TensorProductStrategy` is projective by construction, which is the right definition of the quantum value (`lem:povm-value-eq` says allowing POVMs changes nothing). But a *soundness* argument often has to start from an arbitrary POVM strategy --- blueprint `lem:ms-direct-anticomm` is stated for one, and its whole point is that no projectivity is assumed --- so this file gives the unbundled value of a POVM strategy and the conditional failure probabilities that soundness arguments actually consume. Nothing here is bundled into a…
--
--   **The Born probabilities of a pair of POVMs sum to one.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix Kronecker
--   open scoped ComplexOrder MatrixOrder
--   variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
--   variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
--
--   theorem MIPRE.sum_bornProb {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (MA : POVM A dA)
--       (MB : POVM B dB) :
--       ∑ a, ∑ b, bornProb ψ (((MA.mats a).val)) (((MB.mats b).val)) = 1
--   ```
--
--   **Formalization Note** `MIPRE.sum_bornProb` is declared in `MIPRE/Foundations/POVMValue.lean`, lines 138–162. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/POVMValue.lean#L138-L162

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
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

theorem MIPRE.sum_bornProb {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (MA : POVM A dA)
    (MB : POVM B dB) :
    ∑ a, ∑ b, bornProb ψ (((MA.mats a).val)) (((MB.mats b).val)) = 1 := by sorry
