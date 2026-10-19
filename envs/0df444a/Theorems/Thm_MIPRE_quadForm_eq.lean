-- Prove2me | Theorems.Thm_MIPRE_quadForm_eq
-- name    : MIPRE.quadForm_eq
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:28:53.843268+00:00
-- url     : https://prove2.me/theorems/de3fef0e-fcde-4360-8c2d-705956e4f088
-- title:
--   The squared norm is the blueprint's quadratic form, as a complex number: ⟨ψ| M† M ⊗ Id |ψ⟩ is real and equal to stateSqNorm ψ M
-- statement:
--   A statement of the module `MIPRE.Foundations.StateDistance` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The state-dependent distance on a bipartite state. Every soundness argument in the Pauli basis test's appendix compares operators in the distance `A^x ≈_δ B^x` ⟺ `𝔼_{x ∼ μ} ⟨ψ| (A^x - B^x)† (A^x - B^x) |ψ⟩ ≤ δ`, where the operators act on **Alice's factor** of a bipartite state `|ψ⟩ ∈ ℂ^{dA} ⊗ ℂ^{dB}`. That is not the distance `MIPRE/Foundations/Distances.lean` defines: `povmDistance` and `IsPOVMClose` use the normalized Hilbert--Schmidt norm, which is the *tracial* — synchronous — specialization, and `MIPRE/Foundations/Closeness.lean` says so in its own docstring. This file is the…
--
--   **The squared norm is the blueprint's quadratic form**, as a complex number:
--   `⟨ψ| M† M ⊗ Id |ψ⟩` is real and equal to `stateSqNorm ψ M`. This is the only place the Kronecker
--   adjoint is needed, and it is what makes the Lean definition and `def:state-distance`'s spelling
--   the same object rather than informally the same. The complex form is what a positivity
--   hypothesis on a linear functional wants.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix Kronecker
--   variable {X : Type*} [Fintype X]
--   variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
--
--   theorem MIPRE.quadForm_eq (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
--       star ψ ⬝ᵥ ((((Mᴴ * M) ⊗ₖ (1 : Matrix dB dB ℂ))) *ᵥ ψ) = (stateSqNorm ψ M : ℂ)
--   ```
--
--   **Formalization Note** `MIPRE.quadForm_eq` is declared in `MIPRE/Foundations/StateDistance.lean`, lines 98–120. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/StateDistance.lean#L98-L120; blueprint def:state-distance

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
import Definitions.Def_MIPRE_Foundations_StateDistance

open MIPRE
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]

theorem MIPRE.quadForm_eq (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    star ψ ⬝ᵥ ((((Mᴴ * M) ⊗ₖ (1 : Matrix dB dB ℂ))) *ᵥ ψ) = (stateSqNorm ψ M : ℂ) := by sorry
