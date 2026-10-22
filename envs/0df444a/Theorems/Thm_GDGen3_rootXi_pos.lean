-- Prove2me | Theorems.Thm_GDGen3_rootXi_pos
-- name    : GDGen3.rootXi_pos
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:29:31.846291+00:00
-- url     : https://prove2.me/theorems/6781c22b-beb3-4ee3-a841-5c17ae61b206
-- title:
--   General-N certificate lemma: rootXi_pos
-- statement:
--   Lemma `rootXi_pos` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma rootXi_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) (hi : i ≠ 0) :
    0 < rootXi r N i := by sorry
