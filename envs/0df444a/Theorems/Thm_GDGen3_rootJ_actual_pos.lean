-- Prove2me | Theorems.Thm_GDGen3_rootJ_actual_pos
-- name    : GDGen3.rootJ_actual_pos
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:38:32.190881+00:00
-- url     : https://prove2.me/theorems/2205c1ab-76d7-466f-ae7e-6c6eaab1006f
-- title:
--   General-N certificate lemma: rootJ_actual_pos
-- statement:
--   Lemma `rootJ_actual_pos` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma rootJ_actual_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    0 < rootJ r (M r N) (rootXi r N (i - 1)) i := by sorry
