-- Prove2me | Theorems.Thm_GDGen3_pj_geometric
-- name    : GDGen3.pj_geometric
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:18:10.380599+00:00
-- url     : https://prove2.me/theorems/2aa51eb7-203a-4c44-82af-b604c6b6f101
-- title:
--   General-N certificate lemma: pj_geometric
-- statement:
--   Lemma `pj_geometric` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma pj_geometric (r : ℝ) (hr : r ≠ 0) (j : ℕ) :
    pj r j = ((1 / r ^ 2) ^ j - 1) / 2 := by sorry
