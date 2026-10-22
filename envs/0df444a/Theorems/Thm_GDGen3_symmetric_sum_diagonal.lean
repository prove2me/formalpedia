-- Prove2me | Theorems.Thm_GDGen3_symmetric_sum_diagonal
-- name    : GDGen3.symmetric_sum_diagonal
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T05:59:20.370638+00:00
-- url     : https://prove2.me/theorems/617c4be1-9cda-41ef-a06a-4645e2bb53b2
-- title:
--   General-N certificate lemma: symmetric_sum_diagonal
-- statement:
--   Lemma `symmetric_sum_diagonal` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma symmetric_sum_diagonal (B P : ℕ → ℕ → ℝ) (N : ℕ)
    (hP : ∀ i j, P i j = P j i)
    (hB : ∀ i j, i ≤ N → j ≤ N → i ≠ j → B i j + B j i = 0) :
    (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), B i j * P i j)
      = ∑ i ∈ range (N + 1), B i i * P i i := by sorry
