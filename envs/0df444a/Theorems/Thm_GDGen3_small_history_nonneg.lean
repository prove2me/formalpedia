-- Prove2me | Theorems.Thm_GDGen3_small_history_nonneg
-- name    : GDGen3.small_history_nonneg
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:48:12.322976+00:00
-- url     : https://prove2.me/theorems/c73bf306-806d-46de-aaca-b0bf2ed80e6a
-- title:
--   General-N certificate lemma: small_history_nonneg
-- statement:
--   Lemma `small_history_nonneg` of the general-N certificate (manuscript section 6), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

theorem small_history_nonneg
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hboundary : 1 / r ^ N = 1 + (N : ℝ) * (1 + r))
    (h : ℝ) (hh : 0 < h) (hha : h ≤ 1 + r)
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i)
    (hQ : ∀ i j, i ≤ N → j ≤ N → i ≠ j → 0 ≤ Qv h f P i j)
    (hdiff : ∀ i j, i ≤ N → j ≤ N → 0 ≤ P i i + P j j - 2 * P i j) :
    0 ≤ smallK N h f (fun i => P i i) := by sorry
