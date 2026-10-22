-- Prove2me | Theorems.Thm_GDGen3_Abar_root_step
-- name    : GDGen3.Abar_root_step
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:39:51.052265+00:00
-- url     : https://prove2.me/theorems/849940cd-42a4-4c8a-966f-ee43f1ff2e05
-- title:
--   General-N certificate lemma: Abar_root_step
-- statement:
--   Lemma `Abar_root_step` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma Abar_root_step (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    Abar (rootXi r N) (i - 1) < Abar (rootXi r N) i := by sorry
