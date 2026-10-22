-- Prove2me | Theorems.Thm_GDGen3_Abar_ne_zero
-- name    : GDGen3.Abar_ne_zero
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T05:40:46.965905+00:00
-- url     : https://prove2.me/theorems/2788e10b-c746-4e5d-873c-5f579529975d
-- title:
--   General-N certificate lemma: Abar_ne_zero
-- statement:
--   Lemma `Abar_ne_zero` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma Abar_ne_zero (ξ : ℕ → ℝ) (h0 : ξ 0 = 0) (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) :
    ∀ i : ℕ, Abar ξ i ≠ 0 := by sorry
