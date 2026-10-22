-- Prove2me | Theorems.Thm_GDGen3_optimal_history_identity
-- name    : GDGen3.optimal_history_identity
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:43:30.765621+00:00
-- url     : https://prove2.me/theorems/c35f3fca-1236-4652-95fc-794118f0d24e
-- title:
--   General-N certificate lemma: optimal_history_identity
-- statement:
--   Lemma `optimal_history_identity` of the general-N certificate (manuscript section 6), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma optimal_history_identity (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hboundary : 1 / r ^ N = 1 + (N : ℝ) * (1 + r))
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (hP : ∀ i j, P i j = P j i) :
    (1 + r) * smallK N (1 + r) f (fun i => P i i) =
      2 * (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
        if i = j then 0 else ell r (rootXi r N) N i j * Qv (1 + r) f P i j) := by sorry
