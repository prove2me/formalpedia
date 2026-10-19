-- Prove2me | Theorems.Thm_MIPRE_Introspection_unitaryTwirl_outcome_dist_le
-- name    : MIPRE.Introspection.unitaryTwirl_outcome_dist_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:11:37.917269+00:00
-- url     : https://prove2.me/theorems/a1dd328a-3663-4834-a77d-b8ad391f87f2
-- title:
--   The outcome-summed, question-averaged form, with no alphabet or dimension loss
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.TwirlDistance` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Approximate commutation controls twirling in the state-dependent norm. This is the paper's `lem:mixing-U`, with constant one and all outcome sums explicit. The state need not be invariant under any of the unitaries.
--
--   The outcome-summed, question-averaged form, with no alphabet or dimension loss.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix
--   variable {dA dB I : Type*} [Fintype dA] [DecidableEq dA]
--
--   theorem MIPRE.Introspection.unitaryTwirl_outcome_dist_le {X A : Type*} [Fintype X] [Fintype A]
--       (D : X → ℝ) (hD : ∀ x, 0 ≤ D x)
--       (μ : X → I → ℝ) (hμ0 : ∀ x u, 0 ≤ μ x u) (hμ1 : ∀ x, ∑ u, μ x u = 1)
--       (U : X → I → Matrix dA dA ℂ) (hU : ∀ x u, (U x u)ᴴ * U x u = 1)
--       (ψ : dA × dB → ℂ) (M : X → A → Matrix dA dA ℂ) :
--       (∑ x, D x * ∑ a, stateSqNorm ψ (unitaryTwirl (μ x) (U x) (M x a) - M x a)) ≤
--         ∑ x, D x * ∑ u, μ x u * ∑ a,
--           stateSqNorm ψ (M x a * (U x u)ᴴ - (U x u)ᴴ * M x a)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.unitaryTwirl_outcome_dist_le` is declared in `MIPRE/Foundations/Introspection/TwirlDistance.lean`, lines 58–81. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/TwirlDistance.lean#L58-L81; blueprint lem:pauli-unitary-mixing

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

theorem MIPRE.Introspection.unitaryTwirl_outcome_dist_le {X A : Type*} [Fintype X] [Fintype A]
    (D : X → ℝ) (hD : ∀ x, 0 ≤ D x)
    (μ : X → I → ℝ) (hμ0 : ∀ x u, 0 ≤ μ x u) (hμ1 : ∀ x, ∑ u, μ x u = 1)
    (U : X → I → Matrix dA dA ℂ) (hU : ∀ x u, (U x u)ᴴ * U x u = 1)
    (ψ : dA × dB → ℂ) (M : X → A → Matrix dA dA ℂ) :
    (∑ x, D x * ∑ a, stateSqNorm ψ (unitaryTwirl (μ x) (U x) (M x a) - M x a)) ≤
      ∑ x, D x * ∑ u, μ x u * ∑ a,
        stateSqNorm ψ (M x a * (U x u)ᴴ - (U x u)ᴴ * M x a) := by sorry
