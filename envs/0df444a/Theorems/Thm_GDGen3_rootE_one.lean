-- Prove2me | Theorems.Thm_GDGen3_rootE_one
-- name    : GDGen3.rootE_one
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:36:07.314006+00:00
-- url     : https://prove2.me/theorems/98c03a51-0810-4a19-8b00-754a51b26f2a
-- title:
--   General-N certificate lemma: rootE_one
-- statement:
--   Lemma `rootE_one` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma rootE_one (r : ℝ) (hr : 0 < r) : rootE r 1 = (1 + r) * (1 - r) ^ 2 / r := by sorry
