-- Prove2me | Theorems.Thm_GDGen3_rootNu_neg
-- name    : GDGen3.rootNu_neg
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:35:46.311644+00:00
-- url     : https://prove2.me/theorems/368b90f4-75ff-4f22-b1ea-6895d0293675
-- title:
--   General-N certificate lemma: rootNu_neg
-- statement:
--   Lemma `rootNu_neg` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma rootNu_neg (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) : rootNu r i < 0 := by sorry
