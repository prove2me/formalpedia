-- Prove2me | Theorems.Thm_GDGen3_PiS_next_strict
-- name    : GDGen3.PiS_next_strict
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:25:42.903174+00:00
-- url     : https://prove2.me/theorems/486704ea-2ed1-44f8-a0d6-23dec6e51025
-- title:
--   General-N certificate lemma: PiS_next_strict
-- statement:
--   Lemma `PiS_next_strict` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma PiS_next_strict (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (n : ℕ) (hn : 0 < n) :
    2 * PiS r n < (n : ℝ) * pj r (n + 1) := by sorry
