-- Prove2me | Theorems.Thm_GDGen3_decreasing_sequence_tail
-- name    : GDGen3.decreasing_sequence_tail
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:46:21.607231+00:00
-- url     : https://prove2.me/theorems/5cc11365-8e21-4720-9322-0c61bbfa0f16
-- title:
--   General-N certificate lemma: decreasing_sequence_tail
-- statement:
--   Lemma `decreasing_sequence_tail` of the general-N certificate (manuscript section 6), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma decreasing_sequence_tail (q : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ i, i < N → q (i + 1) ≤ q i) (i : ℕ) (hi : i ≤ N) : q N ≤ q i := by sorry
