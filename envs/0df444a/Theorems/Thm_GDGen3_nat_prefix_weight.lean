-- Prove2me | Theorems.Thm_GDGen3_nat_prefix_weight
-- name    : GDGen3.nat_prefix_weight
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:19:49.139822+00:00
-- url     : https://prove2.me/theorems/826d1a88-4d80-44d0-ab73-70fc2219a6b4
-- title:
--   General-N certificate lemma: nat_prefix_weight
-- statement:
--   Lemma `nat_prefix_weight` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma nat_prefix_weight (n : ℕ) :
    2 * (∑ k ∈ range n, ((k : ℝ) + 1)) = (n : ℝ) * ((n : ℝ) + 1) := by sorry
