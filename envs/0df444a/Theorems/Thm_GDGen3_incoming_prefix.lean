-- Prove2me | Theorems.Thm_GDGen3_incoming_prefix
-- name    : GDGen3.incoming_prefix
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:01:19.099045+00:00
-- url     : https://prove2.me/theorems/12163135-efd4-443f-b527-7b02c197a57c
-- title:
--   General-N certificate lemma: incoming_prefix
-- statement:
--   Lemma `incoming_prefix` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_ell_of_lt
import Theorems.Thm_GDGen3_am_telescope

noncomputable section

open Finset

namespace GDGen3

lemma incoming_prefix (r : ℝ) (ξ : ℕ → ℝ) (N a b : ℕ) (hab : a < b) :
    (∑ i ∈ range (a + 1), ell r ξ N i b) =
      Abar ξ a * (D r ξ N b + r * D r ξ N (b + 1)) := by sorry
