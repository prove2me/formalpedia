-- Prove2me | Theorems.Thm_MIPRE_stateSqNorm_avg_le
-- name    : MIPRE.stateSqNorm_avg_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:38.056499+00:00
-- url     : https://prove2.me/theorems/4bc2d193-bfdc-409b-8e8e-7194f1ca03b5
-- title:
--   Averaging preserves closeness, blueprint lem:qld-averaging: a weighted average with weights of modulus at most one is no further apart than the families are
-- statement:
--   A statement of the module `MIPRE.Foundations.StateDistance` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The state-dependent distance on a bipartite state. Every soundness argument in the Pauli basis test's appendix compares operators in the distance `A^x ≈_δ B^x` ⟺ `𝔼_{x ∼ μ} ⟨ψ| (A^x - B^x)† (A^x - B^x) |ψ⟩ ≤ δ`, where the operators act on **Alice's factor** of a bipartite state `|ψ⟩ ∈ ℂ^{dA} ⊗ ℂ^{dB}`. That is not the distance `MIPRE/Foundations/Distances.lean` defines: `povmDistance` and `IsPOVMClose` use the normalized Hilbert--Schmidt norm, which is the *tracial* — synchronous — specialization, and `MIPRE/Foundations/Closeness.lean` says so in its own docstring. This file is the…
--
--   **Averaging preserves closeness**, blueprint `lem:qld-averaging`: a weighted average with
--   weights of modulus at most one is no further apart than the families are. Triangle inequality,
--   then Jensen for the square root (`sum_mul_sqrt_le`).
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix Kronecker
--   variable {X : Type*} [Fintype X]
--   variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
--
--   theorem MIPRE.stateSqNorm_avg_le {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
--       (ψ : dA × dB → ℂ) (A B : X → Matrix dA dA ℂ) (α : X → ℂ) (hα : ∀ x, ‖α x‖ ≤ 1) :
--       stateSqNorm ψ ((∑ x, ((μ x : ℂ) * α x) • A x) - ∑ x, ((μ x : ℂ) * α x) • B x)
--         ≤ stateDist μ ψ A B
--   ```
--
--   **Formalization Note** `MIPRE.stateSqNorm_avg_le` is declared in `MIPRE/Foundations/StateDistance.lean`, lines 311–342. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/StateDistance.lean#L311-L342; blueprint lem:qld-averaging

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

theorem MIPRE.stateSqNorm_avg_le {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (ψ : dA × dB → ℂ) (A B : X → Matrix dA dA ℂ) (α : X → ℂ) (hα : ∀ x, ‖α x‖ ≤ 1) :
    stateSqNorm ψ ((∑ x, ((μ x : ℂ) * α x) • A x) - ∑ x, ((μ x : ℂ) * α x) • B x)
      ≤ stateDist μ ψ A B := by sorry
