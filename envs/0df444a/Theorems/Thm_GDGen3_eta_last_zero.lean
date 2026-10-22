-- Prove2me | Theorems.Thm_GDGen3_eta_last_zero
-- name    : GDGen3.eta_last_zero
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T05:49:41.804994+00:00
-- url     : https://prove2.me/theorems/84c34df3-795b-4bb0-9460-4c8e3033f7c6
-- title:
--   General-N certificate lemma: eta_last_zero
-- statement:
--   Lemma `eta_last_zero` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_quad_eta

noncomputable section

open Finset

namespace GDGen3

lemma eta_last_zero (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (h0 : ξ 0 = 0)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + ξ i + C r N i) = X r N i)
    (hpin : pj r N * ξ (N - 1) = X r N (N - 1)) :
    eta r N ξ (N - 1) = 0 := by sorry
