-- Prove2me | Theorems.Thm_GDGen3_rootJ_reference_factor
-- name    : GDGen3.rootJ_reference_factor
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:37:15.036722+00:00
-- url     : https://prove2.me/theorems/ef686a93-6b7d-451b-b63a-14b2176c2832
-- title:
--   General-N certificate lemma: rootJ_reference_factor
-- statement:
--   Lemma `rootJ_reference_factor` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma rootJ_reference_factor (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) :
    rootJ r (1 + r) (referenceXi r (i - 1)) i =
      r ^ i * rootE r i / ((1 - r ^ i) * (1 - (r ^ i * r) ^ 2)) := by sorry
