-- Prove2me | Theorems.Thm_GDGen3_sum_suffix_indicator
-- name    : GDGen3.sum_suffix_indicator
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T05:56:57.026947+00:00
-- url     : https://prove2.me/theorems/7a7ab156-9769-4ec1-b6a8-4adaa77001a9
-- title:
--   General-N certificate lemma: sum_suffix_indicator
-- statement:
--   Lemma `sum_suffix_indicator` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma sum_suffix_indicator (F : ℕ → ℝ) (N a : ℕ) :
    (∑ k ∈ range (N + 1), if a < k then F k else 0) = ∑ k ∈ Icc (a + 1) N, F k := by sorry
