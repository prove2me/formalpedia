-- Prove2me | Theorems.Thm_GDGen3_rootPoly_factor
-- name    : GDGen3.rootPoly_factor
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:38:22.64562+00:00
-- url     : https://prove2.me/theorems/21e22917-1b94-453a-9310-2e869d644441
-- title:
--   General-N certificate lemma: rootPoly_factor
-- statement:
--   Lemma `rootPoly_factor` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma rootPoly_factor (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N) :
    rootPoly r (M r N) i (pj r i / pj r (i + 1) * (1 + rootXi r N (i - 1))) =
      pj r i * (1 + rootXi r N (i - 1)) * rootJ r (M r N) (rootXi r N (i - 1)) i := by sorry
