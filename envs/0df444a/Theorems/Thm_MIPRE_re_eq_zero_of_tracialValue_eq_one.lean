-- Prove2me | Theorems.Thm_MIPRE_re_eq_zero_of_tracialValue_eq_one
-- name    : MIPRE.re_eq_zero_of_tracialValue_eq_one
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:16:05.144253+00:00
-- url     : https://prove2.me/theorems/cef2b87b-39e6-4114-bb85-5f6c6c2cae41
-- title:
--   A perfect strategy rejects nothing on the support. If the value is 1 then every rejected answer pair has probability zero at every question pair of positive weight
-- statement:
--   A statement of the module `MIPRE.Foundations.PerfectStrategy` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Perfect strategies reject nothing on the support. Every completeness argument in the pipeline needs the same step: a strategy of value `1` does not merely win on average, it assigns probability zero to each rejected answer pair at each question pair the verifier actually asks. That step was used implicitly inside `MIPRE.tracialValue_le_one` and nowhere available as a lemma; this file states it. * `sum_re_tracial` — at a fixed question pair the outcome probabilities sum to one. This was a `have` inside `tracialValue_le_one`; it is the reason the value is at most one, and it is wanted on its…
--
--   **A perfect strategy rejects nothing on the support.** If the value is `1` then every
--   rejected answer pair has probability zero at every question pair of positive weight.
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
--   theorem MIPRE.re_eq_zero_of_tracialValue_eq_one (G : SynchronousGame X A) (τ : TracialState 𝒜)
--       (P : ProjectiveMeasurement X A 𝒜) (h : tracialValue G τ P = 1)
--       {x y : X} (hxy : 0 < G.μ x y) {a b : A} (hD : G.D x y a b = false) :
--       (τ (P.M x a * P.M y b)).re = 0
--   ```
--
--   **Formalization Note** `MIPRE.re_eq_zero_of_tracialValue_eq_one` is declared in `MIPRE/Foundations/PerfectStrategy.lean`, lines 61–92. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/PerfectStrategy.lean#L61-L92; blueprint lem:perfect-rejects-nothing

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

theorem MIPRE.re_eq_zero_of_tracialValue_eq_one (G : SynchronousGame X A) (τ : TracialState 𝒜)
    (P : ProjectiveMeasurement X A 𝒜) (h : tracialValue G τ P = 1)
    {x y : X} (hxy : 0 < G.μ x y) {a b : A} (hD : G.D x y a b = false) :
    (τ (P.M x a * P.M y b)).re = 0 := by sorry
