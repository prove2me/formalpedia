-- Prove2me | Theorems.Thm_GDGen3_X_pos
-- name    : GDGen3.X_pos
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:28:22.92798+00:00
-- url     : https://prove2.me/theorems/1c18583e-b57b-4acc-9600-f5df7f194ed6
-- title:
--   General-N certificate lemma: X_pos
-- statement:
--   Lemma `X_pos` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma X_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) (hi : 1 ≤ i) (hiN : i < N) :
    0 < X r N i := by sorry
