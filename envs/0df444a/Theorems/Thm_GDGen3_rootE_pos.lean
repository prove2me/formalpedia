-- Prove2me | Theorems.Thm_GDGen3_rootE_pos
-- name    : GDGen3.rootE_pos
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:36:26.00509+00:00
-- url     : https://prove2.me/theorems/de25f7b4-4f94-4bc1-97dc-49a4d910ffbd
-- title:
--   General-N certificate lemma: rootE_pos
-- statement:
--   Lemma `rootE_pos` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma rootE_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) : 0 < rootE r i := by sorry
