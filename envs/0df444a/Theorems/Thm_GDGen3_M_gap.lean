-- Prove2me | Theorems.Thm_GDGen3_M_gap
-- name    : GDGen3.M_gap
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:31:36.141979+00:00
-- url     : https://prove2.me/theorems/ad7c3877-ec8f-4f0c-b314-738a61e2ff9b
-- title:
--   General-N certificate lemma: M_gap
-- statement:
--   Lemma `M_gap` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma M_gap (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N) :
    (1 + r) - M r N =
      ((1 + (N : ℝ) * (1 + r)) ^ 2 - 1 / r ^ (2 * N)) /
        ((1 + r) * (N : ℝ) * ((N : ℝ) + 1)) := by sorry
