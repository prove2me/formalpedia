-- Prove2me | Theorems.Thm_GDGen3_rV_sub_U
-- name    : GDGen3.rV_sub_U
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T05:57:16.995722+00:00
-- url     : https://prove2.me/theorems/a38e783e-a3a6-465c-accc-ce2c92dcd664
-- title:
--   General-N certificate lemma: rV_sub_U
-- statement:
--   Lemma `rV_sub_U` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_Abar_ne_zero
import Theorems.Thm_GDGen3_ell_of_lt
import Theorems.Thm_GDGen3_ell_of_gt
import Theorems.Thm_GDGen3_am_telescope
import Theorems.Thm_GDGen3_D_telescope

noncomputable section

open Finset

namespace GDGen3

theorem rV_sub_U (r : ℝ) (N i : ℕ) (hN : 1 ≤ N) (ξ : ℕ → ℝ) (h0 : ξ 0 = 0)
    (hpos : ∀ i : ℕ, i ≠ 0 → 0 < ξ i) (hr : r ≠ 0) (hi : i + 1 ≤ N) :
    r * V r ξ N i - U r ξ N i = (1 - r ^ 2) / 2 := by sorry
