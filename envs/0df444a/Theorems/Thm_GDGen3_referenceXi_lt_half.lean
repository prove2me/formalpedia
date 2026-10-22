-- Prove2me | Theorems.Thm_GDGen3_referenceXi_lt_half
-- name    : GDGen3.referenceXi_lt_half
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:23:05.743812+00:00
-- url     : https://prove2.me/theorems/0cb36dde-85bf-49c0-9fa9-6a27603e373a
-- title:
--   General-N certificate lemma: referenceXi_lt_half
-- statement:
--   Lemma `referenceXi_lt_half` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma referenceXi_lt_half (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) :
    referenceXi r i < (i : ℝ) / 2 := by sorry
