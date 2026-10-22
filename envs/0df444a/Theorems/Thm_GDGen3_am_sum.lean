-- Prove2me | Theorems.Thm_GDGen3_am_sum
-- name    : GDGen3.am_sum
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T05:51:32.540844+00:00
-- url     : https://prove2.me/theorems/e85ee74d-5fb2-459b-ae4f-5a65b6586801
-- title:
--   General-N certificate lemma: am_sum
-- statement:
--   Lemma `am_sum` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma am_sum (ξ : ℕ → ℝ) (h0 : ξ 0 = 0) : ∀ i : ℕ,
    Finset.sum (Finset.range (i + 1)) (fun k => Am ξ k)
      = Finset.sum (Finset.range i) (fun k => Abar ξ k) := by sorry
