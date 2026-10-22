-- Prove2me | Theorems.Thm_GDGen3_incoming_sum
-- name    : GDGen3.incoming_sum
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:09:13.697072+00:00
-- url     : https://prove2.me/theorems/e7dd23f2-5ac6-4d4f-9718-f7fe0a46aa7f
-- title:
--   General-N certificate lemma: incoming_sum
-- statement:
--   Lemma `incoming_sum` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_sum_suffix_indicator
import Theorems.Thm_GDGen3_total_sub_suffix

noncomputable section

open Finset

namespace GDGen3

lemma incoming_sum (r : ℝ) (ξ : ℕ → ℝ) (N i : ℕ) (hi : i ≤ N) :
    (∑ j ∈ range (N + 1), ell r ξ N j i) = U r ξ N i + ell r ξ N i i + V r ξ N i := by sorry
