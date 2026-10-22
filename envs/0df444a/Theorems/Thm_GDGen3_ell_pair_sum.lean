-- Prove2me | Theorems.Thm_GDGen3_ell_pair_sum
-- name    : GDGen3.ell_pair_sum
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:00:59.149168+00:00
-- url     : https://prove2.me/theorems/d47a64cb-9112-4da7-ad0d-e8570a1467c3
-- title:
--   General-N certificate lemma: ell_pair_sum
-- statement:
--   Lemma `ell_pair_sum` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_ell_of_lt
import Theorems.Thm_GDGen3_ell_of_gt

noncomputable section

open Finset

namespace GDGen3

lemma ell_pair_sum (r : ℝ) (ξ : ℕ → ℝ) (N a b : ℕ) (hab : a < b) :
    ell r ξ N a b + ell r ξ N b a =
      (1 + r) * (Abar ξ a * D r ξ N b - Am ξ a * D r ξ N (b + 1)) := by sorry
