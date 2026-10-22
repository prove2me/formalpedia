-- Prove2me | Theorems.Thm_GDGen3_rootXi_step_scaled
-- name    : GDGen3.rootXi_step_scaled
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:39:16.480343+00:00
-- url     : https://prove2.me/theorems/e949fe2d-54e5-40aa-b459-88273ea65abc
-- title:
--   General-N certificate lemma: rootXi_step_scaled
-- statement:
--   Lemma `rootXi_step_scaled` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma rootXi_step_scaled (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    pj r (i + 1) * rootXi r N i < pj r i * (1 + rootXi r N (i - 1)) := by sorry
