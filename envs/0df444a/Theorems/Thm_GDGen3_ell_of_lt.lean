-- Prove2me | Theorems.Thm_GDGen3_ell_of_lt
-- name    : GDGen3.ell_of_lt
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T05:48:33.373883+00:00
-- url     : https://prove2.me/theorems/ab62efbf-d91e-4607-be3a-19a745ae8a45
-- title:
--   General-N certificate lemma: ell_of_lt
-- statement:
--   Lemma `ell_of_lt` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma ell_of_lt (r : ℝ) (ξ : ℕ → ℝ) (N : ℕ) {k j : ℕ} (h : k < j) :
    ell r ξ N k j = (Abar ξ k - Am ξ k) * (D r ξ N j + r * D r ξ N (j + 1)) := by sorry
