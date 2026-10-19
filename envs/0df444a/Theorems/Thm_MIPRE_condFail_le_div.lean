-- Prove2me | Theorems.Thm_MIPRE_condFail_le_div
-- name    : MIPRE.condFail_le_div
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:12:39.072997+00:00
-- url     : https://prove2.me/theorems/f724dff2-366d-4ead-96e3-f02d7a009a11
-- title:
--   From a failure bound to a bound on one subtest
-- statement:
--   A statement of the module `MIPRE.Foundations.POVMValue` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The value of a POVM strategy, and its conditional failures. `MIPRE.TensorProductStrategy` is projective by construction, which is the right definition of the quantum value (`lem:povm-value-eq` says allowing POVMs changes nothing). But a *soundness* argument often has to start from an arbitrary POVM strategy --- blueprint `lem:ms-direct-anticomm` is stated for one, and its whole point is that no projectivity is assumed --- so this file gives the unbundled value of a POVM strategy and the conditional failure probabilities that soundness arguments actually consume. Nothing here is bundled into a…
--
--   **From a failure bound to a bound on one subtest.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix Kronecker
--   open scoped ComplexOrder MatrixOrder
--   variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
--   variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
--   variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
--
--   theorem MIPRE.condFail_le_div (hψ : star ψ ⬝ᵥ ψ = 1) {ε : ℝ} (hfail : 1 - povmValue G ψ MA MB ≤ ε)
--       {x : X} {y : Y} (hμ : 0 < G.μ x y) :
--       condFail G ψ MA MB x y ≤ ε / G.μ x y
--   ```
--
--   **Formalization Note** `MIPRE.condFail_le_div` is declared in `MIPRE/Foundations/POVMValue.lean`, lines 216–230. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/POVMValue.lean#L216-L230

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
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}

theorem MIPRE.condFail_le_div (hψ : star ψ ⬝ᵥ ψ = 1) {ε : ℝ} (hfail : 1 - povmValue G ψ MA MB ≤ ε)
    {x : X} {y : Y} (hμ : 0 < G.μ x y) :
    condFail G ψ MA MB x y ≤ ε / G.μ x y := by sorry
