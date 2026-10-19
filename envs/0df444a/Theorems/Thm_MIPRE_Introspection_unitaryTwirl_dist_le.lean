-- Prove2me | Theorems.Thm_MIPRE_Introspection_unitaryTwirl_dist_le
-- name    : MIPRE.Introspection.unitaryTwirl_dist_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:10:35.068116+00:00
-- url     : https://prove2.me/theorems/e16d880d-1bf7-4025-9711-8659f9e27a31
-- title:
--   Jensen and left-unitary invariance bound the twirl error by the commutator error
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.TwirlDistance` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Approximate commutation controls twirling in the state-dependent norm. This is the paper's `lem:mixing-U`, with constant one and all outcome sums explicit. The state need not be invariant under any of the unitaries.
--
--   Jensen and left-unitary invariance bound the twirl error by the commutator error.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix
--   variable {dA dB I : Type*} [Fintype dA] [DecidableEq dA]
--
--   theorem MIPRE.Introspection.unitaryTwirl_dist_le (μ : I → ℝ) (hμ0 : ∀ u, 0 ≤ μ u) (hμ1 : ∑ u, μ u = 1)
--       (U : I → Matrix dA dA ℂ) (hU : ∀ u, (U u)ᴴ * U u = 1)
--       (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
--       stateSqNorm ψ (unitaryTwirl μ U M - M) ≤
--         ∑ u, μ u * stateSqNorm ψ (M * (U u)ᴴ - (U u)ᴴ * M)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.unitaryTwirl_dist_le` is declared in `MIPRE/Foundations/Introspection/TwirlDistance.lean`, lines 35–56. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/TwirlDistance.lean#L35-L56; blueprint lem:pauli-unitary-mixing

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
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance

open MIPRE
open MIPRE.Introspection
open Finset Matrix
variable {dA dB I : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB] [Fintype I]

theorem MIPRE.Introspection.unitaryTwirl_dist_le (μ : I → ℝ) (hμ0 : ∀ u, 0 ≤ μ u) (hμ1 : ∑ u, μ u = 1)
    (U : I → Matrix dA dA ℂ) (hU : ∀ u, (U u)ᴴ * U u = 1)
    (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    stateSqNorm ψ (unitaryTwirl μ U M - M) ≤
      ∑ u, μ u * stateSqNorm ψ (M * (U u)ᴴ - (U u)ᴴ * M) := by sorry
