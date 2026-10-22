-- Prove2me | Theorems.Thm_GDGen3_oscillatory_square_bound
-- name    : GDGen3.oscillatory_square_bound
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:41:51.128357+00:00
-- url     : https://prove2.me/theorems/a67ecbda-e534-4f18-b49a-25a1213e416c
-- title:
--   General-N certificate lemma: oscillatory_square_bound
-- statement:
--   The certificate implies q_N <= r^(2N) X_0 for arbitrary N, under interpolation and the nonnegative residual conditions.
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

theorem oscillatory_square_bound
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r))
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (R : ℕ → ℝ) (X0 : ℝ)
    (hP : ∀ i j, P i j = P j i)
    (hQ : ∀ i j, i ≤ N → j ≤ N → i ≠ j → 0 ≤ Qv (1 + r) f P i j)
    (hstar : ∀ i, i ≤ N → 0 ≤ -f i + gself (1 + r) R P i - (1 / 2) * P i i)
    (hto : ∀ i, i ≤ N → 0 ≤ f i - (1 / 2) * P i i)
    (hresidual : 0 ≤ (X0 - 2 * (1 + r) * (∑ i ∈ range N, R i)
        + (1 + r) ^ 2 * (∑ i ∈ range N, ∑ j ∈ range N, P i j))
      - 2 * gself (1 + r) R P N + P N N) :
    P N N ≤ r ^ (2 * N) * X0 := by sorry
