-- Prove2me | Theorems.Thm_GDGen3_pj_step
-- name    : GDGen3.pj_step
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:20:32.869611+00:00
-- url     : https://prove2.me/theorems/a909f9e7-63ae-4abc-b69e-af0f34bd4998
-- title:
--   General-N certificate lemma: pj_step
-- statement:
--   Lemma `pj_step` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma pj_step (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    r ^ 2 * pj r (i + 1) - pj r i = (1 - r ^ 2) / 2 := by sorry
