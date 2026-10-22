-- Prove2me | Theorems.Thm_GDGen3_weighted_ginner
-- name    : GDGen3.weighted_ginner
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:04:57.637851+00:00
-- url     : https://prove2.me/theorems/588d20ed-6ff2-4b15-b7e1-0fdc1fa8f3a1
-- title:
--   General-N certificate lemma: weighted_ginner
-- statement:
--   Lemma `weighted_ginner` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_sum_prefix_indicator

noncomputable section

open Finset

namespace GDGen3

lemma weighted_ginner (h : ℝ) (N : ℕ) (L P : ℕ → ℕ → ℝ) :
    (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), L i j * ginner h P i j) =
      h * ∑ j ∈ range (N + 1), ∑ k ∈ range (N + 1),
        ((if k < j then ∑ i ∈ range (N + 1), L i j else 0)
          - ∑ i ∈ range (N + 1), if k < i then L i j else 0) * P j k := by sorry
