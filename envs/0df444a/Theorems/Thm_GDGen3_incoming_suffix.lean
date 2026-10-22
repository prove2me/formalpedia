-- Prove2me | Theorems.Thm_GDGen3_incoming_suffix
-- name    : GDGen3.incoming_suffix
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:04:15.633121+00:00
-- url     : https://prove2.me/theorems/519adefe-e41c-4272-b949-526bb20db393
-- title:
--   General-N certificate lemma: incoming_suffix
-- statement:
--   Lemma `incoming_suffix` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_ell_of_gt
import Theorems.Thm_GDGen3_D_telescope

noncomputable section

open Finset

namespace GDGen3

lemma incoming_suffix (r : ℝ) (ξ : ℕ → ℝ) (N a b : ℕ)
    (hab : a ≤ b) (hb : b ≤ N) :
    (∑ i ∈ Icc (b + 1) N, ell r ξ N i a) =
      (Am ξ a + r * Abar ξ a) * D r ξ N (b + 1) := by sorry
