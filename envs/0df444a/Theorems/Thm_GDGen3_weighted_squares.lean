-- Prove2me | Theorems.Thm_GDGen3_weighted_squares
-- name    : GDGen3.weighted_squares
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:09:20.601993+00:00
-- url     : https://prove2.me/theorems/cb68c575-f376-49be-8e53-79f6c3445ac1
-- title:
--   General-N certificate lemma: weighted_squares
-- statement:
--   Lemma `weighted_squares` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma weighted_squares (L P : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), L i j * (P i i + P j j)) =
      ∑ i ∈ range (N + 1), (∑ j ∈ range (N + 1), (L i j + L j i)) * P i i := by sorry
