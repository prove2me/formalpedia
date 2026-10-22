-- Prove2me | Theorems.Thm_GDGen3_small_step_square_bound
-- name    : GDGen3.small_step_square_bound
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:47:52.254505+00:00
-- url     : https://prove2.me/theorems/3a8d8135-c00d-4d99-8653-84240b5b870c
-- title:
--   General-N certificate lemma: small_step_square_bound
-- statement:
--   The small-step certificate implies (1+Nh)^2 q_N <= X_0 for arbitrary N, under interpolation, squared-gradient difference nonnegativity, trajectory and terminal conditions.
--
--   Formalization scope: this node is part of the all-horizon algebraic certificate development. Its interpolation, Gram, trajectory, and terminal hypotheses, where present in the formal statement, are explicit inputs. This release does not claim that the full function-class supremum theorem has been assembled in Lean. See the explicit-root identity and both branch bounds for the verified algebraic results.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

theorem small_step_square_bound
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hboundary : 1 / r ^ N = 1 + (N : ℝ) * (1 + r))
    (h : ℝ) (hh : 0 < h) (hha : h ≤ 1 + r)
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (R : ℕ → ℝ) (X0 XN : ℝ)
    (hP : ∀ i j, P i j = P j i)
    (hQ : ∀ i j, i ≤ N → j ≤ N → i ≠ j → 0 ≤ Qv h f P i j)
    (hdiff : ∀ i j, i ≤ N → j ≤ N → 0 ≤ P i i + P j j - 2 * P i j)
    (hstar : ∀ i, i < N → 0 ≤ -f i + gself h R P i - (1 / 2) * P i i)
    (hfN : (1 / 2) * P N N ≤ f N) (hXN : P N N ≤ XN)
    (htrajectory : XN = X0 - 2 * h * (∑ i ∈ range N, R i)
      + h ^ 2 * (∑ i ∈ range N, ∑ j ∈ range N, P i j)) :
    (1 + (N : ℝ) * h) ^ 2 * P N N ≤ X0 := by sorry
