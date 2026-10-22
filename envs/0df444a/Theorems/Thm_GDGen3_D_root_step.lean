-- Prove2me | Theorems.Thm_GDGen3_D_root_step
-- name    : GDGen3.D_root_step
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:41:04.644988+00:00
-- url     : https://prove2.me/theorems/4747bbcb-3f3e-41d8-ac82-ef4f5b02776e
-- title:
--   General-N certificate lemma: D_root_step
-- statement:
--   Lemma `D_root_step` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma D_root_step (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    D r (rootXi r N) N (i + 1) < D r (rootXi r N) N i := by sorry
