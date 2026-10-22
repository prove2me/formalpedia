-- Prove2me | Theorems.Thm_GDGen3_cross_inner
-- name    : GDGen3.cross_inner
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T05:56:20.263153+00:00
-- url     : https://prove2.me/theorems/609675b0-e605-4076-8a91-401963cd51a4
-- title:
--   General-N certificate lemma: cross_inner
-- statement:
--   Lemma `cross_inner` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_am_telescope
import Theorems.Thm_GDGen3_am_telescope2

noncomputable section

open Finset

namespace GDGen3

lemma cross_inner (r : ℝ) (ξ : ℕ → ℝ) (N i j : ℕ)
    (h0 : ξ 0 = 0) (hne : ∀ i : ℕ, i ≠ 0 → ξ i ≠ 0)
    (hij : i < j) (hjN : j ≤ N) :
    Finset.sum (Finset.range (i + 1)) (fun k => ell r ξ N k j - ell r ξ N j k)
      = (D r ξ N j + r * D r ξ N (j + 1)) * Abar ξ i
        - (D r ξ N j - D r ξ N (j + 1))
          * ((Finset.sum (Finset.range i) (fun k => Abar ξ k))
              + r * Abar ξ i
              + r * (Finset.sum (Finset.range i) (fun k => Abar ξ k))) := by sorry
