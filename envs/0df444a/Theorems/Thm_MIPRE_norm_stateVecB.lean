-- Prove2me | Theorems.Thm_MIPRE_norm_stateVecB
-- name    : MIPRE.norm_stateVecB
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:35.615519+00:00
-- url     : https://prove2.me/theorems/0c6f84c0-0505-43e6-a16d-cfc9bfe8dc9e
-- title:
--   Bob's norm is Alice's norm of the swapped state
-- statement:
--   A statement of the module `MIPRE.Foundations.StateDistance` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The state-dependent distance on a bipartite state. Every soundness argument in the Pauli basis test's appendix compares operators in the distance `A^x ≈_δ B^x` ⟺ `𝔼_{x ∼ μ} ⟨ψ| (A^x - B^x)† (A^x - B^x) |ψ⟩ ≤ δ`, where the operators act on **Alice's factor** of a bipartite state `|ψ⟩ ∈ ℂ^{dA} ⊗ ℂ^{dB}`. That is not the distance `MIPRE/Foundations/Distances.lean` defines: `povmDistance` and `IsPOVMClose` use the normalized Hilbert--Schmidt norm, which is the *tracial* — synchronous — specialization, and `MIPRE/Foundations/Closeness.lean` says so in its own docstring. This file is the…
--
--   **Bob's norm is Alice's norm of the swapped state.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix Kronecker
--   variable {X : Type*} [Fintype X]
--   variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
--   variable [DecidableEq dA]
--
--   theorem MIPRE.norm_stateVecB (ψ : dA × dB → ℂ) (N : Matrix dB dB ℂ) :
--       ‖stateVecB ψ N‖ = stateNorm (swapVec ψ) N
--   ```
--
--   **Formalization Note** `MIPRE.norm_stateVecB` is declared in `MIPRE/Foundations/StateDistance.lean`, lines 277–288. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/StateDistance.lean#L277-L288

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B

open MIPRE
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
variable [DecidableEq dA]
omit [DecidableEq dB]

theorem MIPRE.norm_stateVecB (ψ : dA × dB → ℂ) (N : Matrix dB dB ℂ) :
    ‖stateVecB ψ N‖ = stateNorm (swapVec ψ) N := by sorry
