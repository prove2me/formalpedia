-- Prove2me | Theorems.Thm_GDGen3_rootE_step
-- name    : GDGen3.rootE_step
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:36:22.907064+00:00
-- url     : https://prove2.me/theorems/e619c254-73f0-4c6b-ad1d-5837e82f07ae
-- title:
--   General-N certificate lemma: rootE_step
-- statement:
--   Lemma `rootE_step` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma rootE_step (r : ℝ) (hr : 0 < r) (i : ℕ) :
    rootE r (i + 1) - rootE r i = (1 + r) * (1 - r) * (1 / r ^ (i + 1) - 1) := by sorry
