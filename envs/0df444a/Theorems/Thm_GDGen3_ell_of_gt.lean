-- Prove2me | Theorems.Thm_GDGen3_ell_of_gt
-- name    : GDGen3.ell_of_gt
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T05:49:38.981718+00:00
-- url     : https://prove2.me/theorems/74614d85-d271-45bc-9e81-e4f092202b88
-- title:
--   General-N certificate lemma: ell_of_gt
-- statement:
--   Lemma `ell_of_gt` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma ell_of_gt (r : ℝ) (ξ : ℕ → ℝ) (N : ℕ) {k j : ℕ} (h : j < k) :
    ell r ξ N k j = (Am ξ j + r * Abar ξ j) * (D r ξ N k - D r ξ N (k + 1)) := by sorry
