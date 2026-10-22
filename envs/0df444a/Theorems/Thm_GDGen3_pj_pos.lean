-- Prove2me | Theorems.Thm_GDGen3_pj_pos
-- name    : GDGen3.pj_pos
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:17:07.895459+00:00
-- url     : https://prove2.me/theorems/49750c64-75ff-458c-bc05-ce49f2508b31
-- title:
--   General-N certificate lemma: pj_pos
-- statement:
--   Lemma `pj_pos` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma pj_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (j : ℕ) (hj : j ≠ 0) :
    0 < pj r j := by sorry
