-- Prove2me | Theorems.Thm_GDGen3_referenceXi_zero
-- name    : GDGen3.referenceXi_zero
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:32:12.898833+00:00
-- url     : https://prove2.me/theorems/1d74eff5-d991-4d69-b665-7e234dc1f48d
-- title:
--   General-N certificate lemma: referenceXi_zero
-- statement:
--   Lemma `referenceXi_zero` of the general-N certificate (manuscript section 3), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma referenceXi_zero (r : ℝ) (hr : 0 < r) : referenceXi r 0 = 0 := by sorry
