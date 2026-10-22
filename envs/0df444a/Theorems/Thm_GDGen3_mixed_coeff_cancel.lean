-- Prove2me | Theorems.Thm_GDGen3_mixed_coeff_cancel
-- name    : GDGen3.mixed_coeff_cancel
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:06:42.506505+00:00
-- url     : https://prove2.me/theorems/d52d39ef-b14d-43d5-a367-fb86595863de
-- title:
--   General-N certificate lemma: mixed_coeff_cancel
-- statement:
--   Lemma `mixed_coeff_cancel` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_ell_pair_sum
import Theorems.Thm_GDGen3_incoming_prefix
import Theorems.Thm_GDGen3_incoming_suffix

noncomputable section

open Finset

namespace GDGen3

lemma mixed_coeff_cancel (r : ℝ) (ξ : ℕ → ℝ) (N a b : ℕ)
    (hab : a < b) (hb : b ≤ N) :
    ell r ξ N a b + ell r ξ N b a =
      (1 + r) * ((∑ i ∈ range (a + 1), ell r ξ N i b)
        - ∑ i ∈ Icc (b + 1) N, ell r ξ N i a) := by sorry
