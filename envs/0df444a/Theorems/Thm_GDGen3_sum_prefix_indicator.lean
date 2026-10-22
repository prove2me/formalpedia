-- Prove2me | Theorems.Thm_GDGen3_sum_prefix_indicator
-- name    : GDGen3.sum_prefix_indicator
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T05:56:39.911394+00:00
-- url     : https://prove2.me/theorems/0ca55d80-71f7-46ff-95df-d73fbbacacd7
-- title:
--   General-N certificate lemma: sum_prefix_indicator
-- statement:
--   Lemma `sum_prefix_indicator` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma sum_prefix_indicator (F : ℕ → ℝ) (B a : ℕ) (ha : a ≤ B) :
    (∑ k ∈ range B, if k < a then F k else 0) = ∑ k ∈ range a, F k := by sorry
