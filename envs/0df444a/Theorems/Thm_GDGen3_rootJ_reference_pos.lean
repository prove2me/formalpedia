-- Prove2me | Theorems.Thm_GDGen3_rootJ_reference_pos
-- name    : GDGen3.rootJ_reference_pos
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:37:21.873923+00:00
-- url     : https://prove2.me/theorems/f2a10fc3-a78d-4f96-a777-be988c26e0bd
-- title:
--   General-N certificate lemma: rootJ_reference_pos
-- statement:
--   Lemma `rootJ_reference_pos` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma rootJ_reference_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) :
    0 < rootJ r (1 + r) (referenceXi r (i - 1)) i := by sorry
