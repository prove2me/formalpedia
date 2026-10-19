-- Prove2me | Theorems.Thm_MIPRE_sum_kronecker_left
-- name    : MIPRE.sum_kronecker_left
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:12:38.898246+00:00
-- url     : https://prove2.me/theorems/b3765dd3-328b-4ec3-9453-7ade652510ac
-- title:
--   Lemma sum_kronecker_left of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.POVMValue` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The value of a POVM strategy, and its conditional failures. `MIPRE.TensorProductStrategy` is projective by construction, which is the right definition of the quantum value (`lem:povm-value-eq` says allowing POVMs changes nothing). But a *soundness* argument often has to start from an arbitrary POVM strategy --- blueprint `lem:ms-direct-anticomm` is stated for one, and its whole point is that no projectivity is assumed --- so this file gives the unbundled value of a POVM strategy and the conditional failure probabilities that soundness arguments actually consume. Nothing here is bundled into a…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix Kronecker
--   open scoped ComplexOrder MatrixOrder
--
--   theorem MIPRE.sum_kronecker_left {dA dB ι : Type*} (s : Finset ι) (f : ι → Matrix dA dA ℂ)
--       (N : Matrix dB dB ℂ) : (∑ i ∈ s, f i) ⊗ₖ N = ∑ i ∈ s, f i ⊗ₖ N
--   ```
--
--   **Formalization Note** `MIPRE.sum_kronecker_left` is declared in `MIPRE/Foundations/POVMValue.lean`, lines 65–71. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/POVMValue.lean#L65-L71

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

theorem MIPRE.sum_kronecker_left {dA dB ι : Type*} (s : Finset ι) (f : ι → Matrix dA dA ℂ)
    (N : Matrix dB dB ℂ) : (∑ i ∈ s, f i) ⊗ₖ N = ∑ i ∈ s, f i ⊗ₖ N := by sorry
