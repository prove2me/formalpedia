-- Prove2me | Theorems.Thm_GDGen3_rootPoly_expanded
-- name    : GDGen3.rootPoly_expanded
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:23:38.514529+00:00
-- url     : https://prove2.me/theorems/fce7cbbf-a58d-468e-89d7-af80fa102230
-- title:
--   General-N certificate lemma: rootPoly_expanded
-- statement:
--   Lemma `rootPoly_expanded` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_pj_pos

noncomputable section

open Finset

namespace GDGen3

lemma rootPoly_expanded (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (v x : ℝ) (i : ℕ) :
    rootPoly r v i x = pj r (i + 1) * x * (1 + x - (1 - r) / (1 + r))
      + v * (i + 1) * x / (1 + r) - v * (i : ℝ) * (i + 1) / (2 * (1 + r))
      + (1 - r) * PiS r i / (1 + r) := by sorry
