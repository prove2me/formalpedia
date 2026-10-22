-- Prove2me | Theorems.Thm_GDGen3_internal_reduction
-- name    : GDGen3.internal_reduction
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:22:28.11658+00:00
-- url     : https://prove2.me/theorems/4f7588ec-94f6-489b-8f9e-1b86d1e07b68
-- title:
--   General-N certificate lemma: internal_reduction
-- statement:
--   Lemma `internal_reduction` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_rV_sub_U
import Theorems.Thm_GDGen3_internal_coefficients
import Theorems.Thm_GDGen3_diagonal_coeff
import Theorems.Thm_GDGen3_flow_at_index
import Theorems.Thm_GDGen3_flow_total
import Theorems.Thm_GDGen3_U_last
import Theorems.Thm_GDGen3_V_last
import Theorems.Thm_GDGen3_pj_zpow

noncomputable section

open Finset

namespace GDGen3

theorem internal_reduction
    (r : ℝ) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (h0 : ξ 0 = 0)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + eta r N ξ i) = X r N i)
    (hquad7 : ∀ i : ℕ, i < N → pj r (i + 1) * eta r N ξ i * (1 + ξ i) = X r N (i + 1))
    (hpin : pj r N * ξ (N - 1) = X r N (N - 1))
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i) :
    2 * Finset.sum (Finset.range (N + 1)) (fun i =>
        Finset.sum (Finset.range (N + 1)) (fun j =>
          if i = j then 0 else ell r ξ N i j * Qv (1 + r) f P i j))
      = 2 * M r N * Finset.sum (Finset.range N) (fun i => f i - f N)
        + (1 - r ^ 2 - M r N) * Finset.sum (Finset.range N) (fun i => P i i)
        + ((N : ℝ) * M r N - r ^ (-(2 * (N : ℤ))) + 1) * P N N := by sorry
