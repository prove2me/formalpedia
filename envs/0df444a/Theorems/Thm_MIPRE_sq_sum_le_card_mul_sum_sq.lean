-- Prove2me | Theorems.Thm_MIPRE_sq_sum_le_card_mul_sum_sq
-- name    : MIPRE.sq_sum_le_card_mul_sum_sq
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:54:42.980565+00:00
-- url     : https://prove2.me/theorems/1124f16c-1e2b-49cb-a6e8-695b73da7cca
-- title:
--   (∑ t)² ≤ n ∑ t², Cauchy--Schwarz against the constant 1
-- statement:
--   A statement of the module `MIPRE.Foundations.Closeness` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The Hilbert--Schmidt closeness calculus. Every soundness argument in the pipeline compares two families of operators in the *state-dependent* distance `∑_a ‖(M_a - N_a)|ψ⟩‖²` and then passes from closeness of the families to closeness of the values, losing a square root. For a *synchronous* strategy the state is the normalized trace itself, so that distance is the normalized Hilbert--Schmidt distance of `MIPRE/Foundations/Distances.lean`, and the whole calculus follows from Cauchy--Schwarz for `MIPRE.hsInner`. This file is that calculus, and nothing about games. * `MIPRE.ntr` — the real part…
--
--   `(∑ t)² ≤ n ∑ t²`, Cauchy--Schwarz against the constant `1`. This is the form the
--   outcome-set steps use: a sum over the answers costs a factor `|𝒜|` when squared.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset ComplexOrder Matrix
--   variable {n : Type*} [Fintype n]
--
--   theorem MIPRE.sq_sum_le_card_mul_sum_sq {ι : Type*} [Fintype ι] (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
--       (∑ i, t i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, t i ^ 2
--   ```
--
--   **Formalization Note** `MIPRE.sq_sum_le_card_mul_sum_sq` is declared in `MIPRE/Foundations/Closeness.lean`, lines 435–449. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Closeness.lean#L435-L449

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness

open MIPRE
open Finset ComplexOrder Matrix
variable {n : Type*} [Fintype n]

theorem MIPRE.sq_sum_le_card_mul_sum_sq {ι : Type*} [Fintype ι] (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
    (∑ i, t i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, t i ^ 2 := by sorry
