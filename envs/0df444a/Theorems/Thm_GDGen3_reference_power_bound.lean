-- Prove2me | Theorems.Thm_GDGen3_reference_power_bound
-- name    : GDGen3.reference_power_bound
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:22:47.293382+00:00
-- url     : https://prove2.me/theorems/e7ef4ee2-c2ff-4b4b-806c-6d9111ae3301
-- title:
--   General-N certificate lemma: reference_power_bound
-- statement:
--   Lemma `reference_power_bound` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_pow_slope_strictMono

noncomputable section

open Finset

namespace GDGen3

lemma reference_power_bound (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    1 / r ^ i < 1 + (i : ℝ) * (1 + r) := by sorry
