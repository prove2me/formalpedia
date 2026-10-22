-- Prove2me | Theorems.Thm_GDGen3_internal_coefficients
-- name    : GDGen3.internal_coefficients
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:12:16.795988+00:00
-- url     : https://prove2.me/theorems/60d6d23e-d179-49c9-977f-f59e9c4c0eb6
-- title:
--   General-N certificate lemma: internal_coefficients
-- statement:
--   Lemma `internal_coefficients` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_sum_suffix_indicator
import Theorems.Thm_GDGen3_symmetric_sum_diagonal
import Theorems.Thm_GDGen3_weighted_ginner
import Theorems.Thm_GDGen3_mixed_coeff_cancel
import Theorems.Thm_GDGen3_total_sub_suffix
import Theorems.Thm_GDGen3_weighted_function_values
import Theorems.Thm_GDGen3_weighted_squares

noncomputable section

open Finset

namespace GDGen3

lemma internal_coefficients (r : ℝ) (ξ : ℕ → ℝ) (N : ℕ)
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i) :
    2 * (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
      if i = j then 0 else ell r ξ N i j * Qv (1 + r) f P i j) =
    ∑ i ∈ range (N + 1), (2 * d r ξ N i * f i
      + (2 * (1 + r) * V r ξ N i - (∑ j ∈ range (N + 1),
          (ell r ξ N i j + ell r ξ N j i)) + 2 * ell r ξ N i i) * P i i) := by sorry
