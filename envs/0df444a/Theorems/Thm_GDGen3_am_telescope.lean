-- Prove2me | Theorems.Thm_GDGen3_am_telescope
-- name    : GDGen3.am_telescope
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T05:51:42.875858+00:00
-- url     : https://prove2.me/theorems/18faf1c3-d2a4-4f5f-9c65-434b99872878
-- title:
--   General-N certificate lemma: am_telescope
-- statement:
--   Lemma `am_telescope` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

namespace GDGen3

lemma am_telescope (ξ : ℕ → ℝ) : ∀ i : ℕ,
    Finset.sum (Finset.range (i + 1)) (fun k => Abar ξ k - Am ξ k) = Abar ξ i := by sorry
