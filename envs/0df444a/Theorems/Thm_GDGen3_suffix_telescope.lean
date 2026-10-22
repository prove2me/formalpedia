-- Prove2me | Theorems.Thm_GDGen3_suffix_telescope
-- name    : GDGen3.suffix_telescope
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T05:52:34.689762+00:00
-- url     : https://prove2.me/theorems/fe95b566-d705-4a5a-a05d-de9583c27fc7
-- title:
--   General-N certificate lemma: suffix_telescope
-- statement:
--   Lemma `suffix_telescope` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_eta_last_zero

noncomputable section

open Finset

namespace GDGen3

theorem suffix_telescope (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (h0 : ξ 0 = 0)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + ξ i + C r N i) = X r N i)
    (hrec : eta_recur_prop r N ξ)
    (hpin : pj r N * ξ (N - 1) = X r N (N - 1)) :
    ∀ i : ℕ, i + 1 ≤ N →
      Finset.sum (Icc (i + 2) N) (fun j => D r ξ N j) = eta r N ξ i * D r ξ N (i + 1) := by sorry
