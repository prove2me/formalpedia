-- Prove2me | Theorems.Thm_GDGen3_optimal_history_nonneg
-- name    : GDGen3.optimal_history_nonneg
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:43:49.555981+00:00
-- url     : https://prove2.me/theorems/e939d3e6-de41-4f34-a767-66426ab4ce17
-- title:
--   General-N certificate lemma: optimal_history_nonneg
-- statement:
--   Lemma `optimal_history_nonneg` of the general-N certificate (manuscript section 6), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

theorem optimal_history_nonneg (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hboundary : 1 / r ^ N = 1 + (N : ℝ) * (1 + r))
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i)
    (hQ : ∀ i j, i ≤ N → j ≤ N → i ≠ j → 0 ≤ Qv (1 + r) f P i j) :
    0 ≤ smallK N (1 + r) f (fun i => P i i) := by sorry
