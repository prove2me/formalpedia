-- Prove2me | Theorems.Thm_GDGen3_X_step
-- name    : GDGen3.X_step
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:21:45.315289+00:00
-- url     : https://prove2.me/theorems/72be58ac-f1b4-4c14-803d-351717a4a69d
-- title:
--   General-N certificate lemma: X_step
-- statement:
--   Lemma `X_step` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_pj_pos

noncomputable section

open Finset

namespace GDGen3

lemma X_step (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) :
    X r N (i + 1) - X r N i = pj r (i + 1) * C r N i := by sorry
