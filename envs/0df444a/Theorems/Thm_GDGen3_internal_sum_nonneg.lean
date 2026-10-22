-- Prove2me | Theorems.Thm_GDGen3_internal_sum_nonneg
-- name    : GDGen3.internal_sum_nonneg
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:43:22.689504+00:00
-- url     : https://prove2.me/theorems/3b03abc7-222f-43c4-b824-c84ee79a9b70
-- title:
--   General-N certificate lemma: internal_sum_nonneg
-- statement:
--   Lemma `internal_sum_nonneg` of the general-N certificate (manuscript section 6), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma internal_sum_nonneg (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, i ≤ N → j ≤ N → i ≠ j → 0 ≤ Qv (1 + r) f P i j) :
    0 ≤ 2 * (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
      if i = j then 0 else ell r (rootXi r N) N i j * Qv (1 + r) f P i j) := by sorry
