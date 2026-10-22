-- Prove2me | Theorems.Thm_GDGen3_total_sub_suffix
-- name    : GDGen3.total_sub_suffix
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:03:59.790985+00:00
-- url     : https://prove2.me/theorems/235ab4b7-22f4-4a19-949e-526be7dbc93c
-- title:
--   General-N certificate lemma: total_sub_suffix
-- statement:
--   Lemma `total_sub_suffix` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_sum_prefix_indicator

noncomputable section

open Finset

namespace GDGen3

lemma total_sub_suffix (F : ℕ → ℝ) (N a : ℕ) (ha : a ≤ N) :
    (∑ i ∈ range (N + 1), F i) - (∑ i ∈ range (N + 1), if a < i then F i else 0)
      = ∑ i ∈ range (a + 1), F i := by sorry
