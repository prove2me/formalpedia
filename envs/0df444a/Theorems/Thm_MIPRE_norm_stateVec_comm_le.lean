-- Prove2me | Theorems.Thm_MIPRE_norm_stateVec_comm_le
-- name    : MIPRE.norm_stateVec_comm_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:08:52.043554+00:00
-- url     : https://prove2.me/theorems/1f490082-6529-4f58-b140-de7ccc4021fc
-- title:
--   Lemma norm_stateVec_comm_le of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.CrossConsistency` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Cross-party consistency, and what winning a subtest buys. The Pauli appendix's `≃_δ` compares `A ⊗ Id` with `Id ⊗ B`: one player's operator against the *other* player's. `MIPRE.stateDist` of `def:state-distance` compares two families on the same side, which is what the orthonormalization step needs; this file is the cross-party form, and the one lemma that produces it.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix Kronecker
--   open scoped ComplexOrder MatrixOrder
--   variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
--   variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
--   variable {ε : ℝ}
--   variable {ψ : dA × dB → ℂ}
--
--   theorem MIPRE.norm_stateVec_comm_le (A B : Matrix dA dA ℂ) (A' B' : Matrix dB dB ℂ)
--       (hA : Aᴴ * A ≤ (1 : Matrix dA dA ℂ)) (hB : Bᴴ * B ≤ (1 : Matrix dA dA ℂ))
--       (hA' : A'ᴴ * A' ≤ (1 : Matrix dB dB ℂ)) (hB' : B'ᴴ * B' ≤ (1 : Matrix dB dB ℂ)) :
--       ‖stateVec ψ (A * B - B * A)‖
--         ≤ 2 * xNorm ψ A A' + 2 * xNorm ψ B B' + ‖stateVecB ψ (B' * A' - A' * B')‖
--   ```
--
--   **Formalization Note** `MIPRE.norm_stateVec_comm_le` is declared in `MIPRE/Foundations/CrossConsistency.lean`, lines 736–771. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CrossConsistency.lean#L736-L771; blueprint def:cross-distance

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B

open MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}

theorem MIPRE.norm_stateVec_comm_le (A B : Matrix dA dA ℂ) (A' B' : Matrix dB dB ℂ)
    (hA : Aᴴ * A ≤ (1 : Matrix dA dA ℂ)) (hB : Bᴴ * B ≤ (1 : Matrix dA dA ℂ))
    (hA' : A'ᴴ * A' ≤ (1 : Matrix dB dB ℂ)) (hB' : B'ᴴ * B' ≤ (1 : Matrix dB dB ℂ)) :
    ‖stateVec ψ (A * B - B * A)‖
      ≤ 2 * xNorm ψ A A' + 2 * xNorm ψ B B' + ‖stateVecB ψ (B' * A' - A' * B')‖ := by sorry
