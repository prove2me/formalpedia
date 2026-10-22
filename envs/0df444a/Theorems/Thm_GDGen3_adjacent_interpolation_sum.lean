-- Prove2me | Theorems.Thm_GDGen3_adjacent_interpolation_sum
-- name    : GDGen3.adjacent_interpolation_sum
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:45:41.051319+00:00
-- url     : https://prove2.me/theorems/e6ad582a-48e9-47a0-927d-d1a2c55d829e
-- title:
--   General-N certificate lemma: adjacent_interpolation_sum
-- statement:
--   Lemma `adjacent_interpolation_sum` of the general-N certificate (manuscript section 6), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma adjacent_interpolation_sum (h : ℝ) (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ)
    (hP : ∀ i j, P i j = P j i) (i : ℕ) :
    2 * (Qv h f P i (i + 1) + Qv h f P (i + 1) i) =
      h * (P i i - P (i + 1) (i + 1))
        - (2 - h) * (P i i + P (i + 1) (i + 1) - 2 * P i (i + 1)) := by sorry
