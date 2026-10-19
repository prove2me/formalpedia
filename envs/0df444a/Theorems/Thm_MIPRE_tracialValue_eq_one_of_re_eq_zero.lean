-- Prove2me | Theorems.Thm_MIPRE_tracialValue_eq_one_of_re_eq_zero
-- name    : MIPRE.tracialValue_eq_one_of_re_eq_zero
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:16:07.142311+00:00
-- url     : https://prove2.me/theorems/231df5a4-f42b-44b1-860e-2fd6d9701987
-- title:
--   The converse: if every rejected answer pair has probability zero at every question pair of positive weight, the value is 1
-- statement:
--   A statement of the module `MIPRE.Foundations.PerfectStrategy` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Perfect strategies reject nothing on the support. Every completeness argument in the pipeline needs the same step: a strategy of value `1` does not merely win on average, it assigns probability zero to each rejected answer pair at each question pair the verifier actually asks. That step was used implicitly inside `MIPRE.tracialValue_le_one` and nowhere available as a lemma; this file states it. * `sum_re_tracial` — at a fixed question pair the outcome probabilities sum to one. This was a `have` inside `tracialValue_le_one`; it is the reason the value is at most one, and it is wanted on its…
--
--   The converse: if every rejected answer pair has probability zero at every question pair
--   of positive weight, the value is `1`. Completeness arguments go this way -- one builds a
--   strategy, checks it never produces a rejected outcome, and concludes.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset
--   open scoped ComplexOrder
--   variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
--   variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
--
--   theorem MIPRE.tracialValue_eq_one_of_re_eq_zero (G : SynchronousGame X A) (τ : TracialState 𝒜)
--       (P : ProjectiveMeasurement X A 𝒜)
--       (h : ∀ x y, 0 < G.μ x y → ∀ a b, G.D x y a b = false →
--         (τ (P.M x a * P.M y b)).re = 0) :
--       tracialValue G τ P = 1
--   ```
--
--   **Formalization Note** `MIPRE.tracialValue_eq_one_of_re_eq_zero` is declared in `MIPRE/Foundations/PerfectStrategy.lean`, lines 94–129. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/PerfectStrategy.lean#L94-L129

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy

open MIPRE
open Finset
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]

theorem MIPRE.tracialValue_eq_one_of_re_eq_zero (G : SynchronousGame X A) (τ : TracialState 𝒜)
    (P : ProjectiveMeasurement X A 𝒜)
    (h : ∀ x y, 0 < G.μ x y → ∀ a b, G.D x y a b = false →
      (τ (P.M x a * P.M y b)).re = 0) :
    tracialValue G τ P = 1 := by sorry
