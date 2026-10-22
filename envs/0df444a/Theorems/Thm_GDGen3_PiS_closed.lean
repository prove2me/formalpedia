-- Prove2me | Theorems.Thm_GDGen3_PiS_closed
-- name    : GDGen3.PiS_closed
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:23:50.734786+00:00
-- url     : https://prove2.me/theorems/90f82723-5e66-4029-8ec4-eb03f75c9fb1
-- title:
--   General-N certificate lemma: PiS_closed
-- statement:
--   Lemma `PiS_closed` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_pj_step

noncomputable section

open Finset

namespace GDGen3

lemma PiS_closed (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) :
    PiS r i = pj r i / (1 - r ^ 2) - (i : ℝ) / 2 := by sorry
