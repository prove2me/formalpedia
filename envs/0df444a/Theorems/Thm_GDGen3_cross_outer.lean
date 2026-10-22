-- Prove2me | Theorems.Thm_GDGen3_cross_outer
-- name    : GDGen3.cross_outer
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T05:54:53.677836+00:00
-- url     : https://prove2.me/theorems/9b9dc256-f128-4524-8b9a-f28705f9abf3
-- title:
--   General-N certificate lemma: cross_outer
-- statement:
--   Lemma `cross_outer` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_prefix_telescope
import Theorems.Thm_GDGen3_D_telescope

noncomputable section

open Finset

namespace GDGen3

lemma cross_outer (r : ℝ) (ξ : ℕ → ℝ) (N i : ℕ) (hi : i + 1 ≤ N)
    (h0 : ξ 0 = 0) (hne : ∀ i : ℕ, i ≠ 0 → ξ i ≠ 0) :
    Finset.sum (Finset.Icc (i + 1) N)
        (fun j => (D r ξ N j + r * D r ξ N (j + 1)) * Abar ξ i
          - (D r ξ N j - D r ξ N (j + 1))
            * ((Finset.sum (Finset.range i) (fun k => Abar ξ k)) + r * Abar ξ i
                + r * (Finset.sum (Finset.range i) (fun k => Abar ξ k))))
      = (1 - r) * (Abar ξ i * D r ξ N (i + 1))
        + (1 + r) * (Abar ξ i * (Finset.sum (Finset.Icc (i + 2) N) (fun j => D r ξ N j))
            - D r ξ N (i + 1) * (Finset.sum (Finset.range i) (fun k => Abar ξ k))) := by sorry
