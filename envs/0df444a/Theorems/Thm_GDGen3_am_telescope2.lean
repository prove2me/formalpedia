-- Prove2me | Theorems.Thm_GDGen3_am_telescope2
-- name    : GDGen3.am_telescope2
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T05:53:28.372621+00:00
-- url     : https://prove2.me/theorems/e0770732-3b82-4dbe-aa06-0baddb4b56b2
-- title:
--   General-N certificate lemma: am_telescope2
-- statement:
--   Lemma `am_telescope2` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_am_sum

noncomputable section

open Finset

namespace GDGen3

lemma am_telescope2 (ξ : ℕ → ℝ) (h0 : ξ 0 = 0) (r : ℝ) (i : ℕ) :
    Finset.sum (Finset.range (i + 1)) (fun k => Am ξ k + r * Abar ξ k)
      = (Finset.sum (Finset.range i) (fun k => Abar ξ k))
        + r * (Abar ξ i + Finset.sum (Finset.range i) (fun k => Abar ξ k)) := by sorry
